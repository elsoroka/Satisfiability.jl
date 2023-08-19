" flatten reshapes arrays of arbitrary # dimensions to 1D arrays."
flatten(a::Array{T}) where T = reshape(a, length(a))


"Flatten nested arrays to a single expression using operator to combine them.
For example, [z1, [z2, z3], z4] with operator and returns and(z1, and(z2, z3), z4).
This is a helper function designed to be called by save! or sat!"
function __flatten_nested_exprs(operator::Function, zs::Vararg{Union{Array{T}, T}}) where T <: AbstractExpr
    # Combine the array exprs so we don't have arrays in arrays
    zs = map( (z) -> isa(z, AbstractExpr) ? z : operator(z), zs)
    return and(collect(zs)) # collect turns it from a tuple to an array
end

"Clean up types in mixed type operations, e.g. and() and sum() which can receive mixed type exprs,"
function __check_inputs_nary_op(zs_mixed::Array{T}; const_type=Bool, expr_type=AbstractExpr) where T
    # Check for wrong type inputs
    if any((z) -> !(isa(z, const_type) || isa(z, expr_type)), zs_mixed)
        return nothing, nothing
    end
    # separate literals and const_type
    literals = filter((z) -> isa(z, const_type), zs_mixed)
    zs = Array{expr_type}(filter((z) -> isa(z, expr_type), zs_mixed))
    return zs, literals
end

# this is a very generic function to combine children of operands in any theory
function __combine(zs::Array{T}, op::Symbol, __is_commutative=false, __try_flatten=false) where T <: AbstractExpr
    if length(zs) == 0
        error("Cannot iterate over zero-length array.")
    elseif length(zs) == 1
        if __try_flatten && zs[1].op == op
            return zs[1].children, zs[1].name
        else
            return zs[1:1], zs[1].name
        end
    end

    # Now we need to take an array of statements and decide how to combine them
    # if this is an op where it makes sense to flatten (eg, and(and(x,y), and(y,z)) then flatten it)
    ops = getproperty.(zs, :op)
    if __try_flatten && (all(ops .== op) ||
                         (__is_commutative && all(map( (o) -> o in [:identity, :const, op], ops))))
        # Returm a combined operator
        # this line merges childless operators and children, eg and(x, and(y,z)) yields [x, y, z]
        children = cat(map( (e) -> length(e.children) > 0 ? e.children : [e], zs)..., dims=1)
    else # op doesn't match, so we won't flatten it
        children = zs
    end
    if __is_commutative
        children = sort(children, by=(c) -> c.name)
    end
    name = __get_hash_name(op, children, is_commutative=__is_commutative)
    
    return children, name
end

"combine(z, op) where z is an n x m matrix of BoolExprs first flattens z, then combines it with op.
combine([z1 z2; z3 z4], or) = or([z1; z2; z3; z4])."
__combine(zs::Matrix{T}, op::Symbol, __is_commutative=false, __try_flatten=false) where T <: AbstractExpr = __combine(flatten(zs), op, __is_commutative, __try_flatten)


"is_permutation(a::Array, b::Array) returns True if a is a permutation of b.
is_permutation([1,2,3], [3,2,1]) == true
is_permutation([1,2,3], [1,3]) == false"
function __is_permutation(a::Array, b::Array)
    return length(a) == length(b) && all(map( (c) -> c in b, a))
end


"Push item into array if item is not already in array.
a = [1,2,3]; push_unique!(a, 4) sets a = [1,2,3,4].
a = [1,2,3]; push_unique!(a, 2) sets a = [1,2,3]."
function push_unique!(array::Array{T}, item::T) where T
# I timed checking if something is in an array and it seems to be efficient for strings.
    return !(item  in array) ? push!(array, item) : array
end


"Append items into array without adding any duplicates."
function append_unique!(array1::Array{T}, array2::Array{T}) where T
    append!(array1, filter( (item) -> !(item in array1), array2))
end


##### PARSING SMT OUTPUT #####

# Given a string consisting of a set of statements (statement-1) \n(statement-2) etc, split into an array of strings, stripping \n and ().
# Split one level only, so "(a(b))(c)(d)" returns ["a(b)", "c", "d"]
# A mismatched left parenthesis like "(a)(bb" generates a warning and the output ["a", "b"]
# A mismatched right parenthesis like "(a)b)" generates no warning and the output ["a"]
function __split_statements(input::AbstractString)
    statements = AbstractString[]
    ptr = findfirst('(', input)
    if isnothing(ptr)
        @error "Unable to split string\n\"$input\""
        return [input]
    end
    # if we get here we found a (
    while !isnothing(ptr)
        stack = 1 # stack tracks how many levels of () there are
        start = ptr
        while stack > 0
            l = findnext('(', input, ptr+1)
            r = findnext(')', input, ptr+1)
            l = isnothing(l) ? length(input) : l
            if isnothing(r)
                #@warn "( at character $ptr without matching )"
                r = length(input)
            end

            # if we found a left parenthesis, add one level and if it's right, subtract one level
            if l < r
                stack += 1
                ptr = l
            else
                stack -= 1
                ptr = r
            end
        end

        push!(statements, input[start+1:ptr-1]) # +1 and -1 strips the ( and )
        ptr = findnext('(', input, ptr+1) # will be nothing if no more (
    end
    return statements
end


# top level parser for SMT output
function parse_smt_output(original_output::AbstractString)
    assignments = Dict()
    # recall the whole output will be surrounded by ()
    output = __split_statements(original_output)
    if length(output) > 1 # something is wrong!
        @error "Unable to parse output\n\"$original_output\""
        return assignments
    end
    # now we've cleared the outer (), so iterating will go over each line in the model
    for line in __split_statements(output[1])
        name, type, value = parse_smt_statement(line)
        if !isnothing(value)
            assignments[name] = value
        end
    end
    return assignments
end

# parse a string corresponding to an SMT-LIB type
function parse_type(type::AbstractString)
    if startswith(type, "(") # it's a fancy type like (_ BitVec 16)
        result = match(r"\(_\s([a-zA-Z]+)\s([0-9]+)\)", type)
        if any(isnothing.(result.captures))
            @error "Unable to parse SMT-LIB type \"$type\""
        end
        if result.captures[1] == "BitVec"
            return nextsize(parse(Int, result.captures[2]))
        end
        # we shouldn't get here
        @error "Unknown SMT-LIB type \"type\""
    else # simple type like "Bool" or "Real"
        types = Dict("Bool" => Bool, "Int" => Int, "Real" => Float64)
        return types[type]
    end
end

# parse a string corresponding to an SMT-LIB value, and if it has no variables, return the numeric value
function parse_return_root_values(value::AbstractString)
    if value == "true"
        return true, 4
    elseif value == "false"
        return false, 5
    end
    # First check if it's a simple number, eg 1 or 2.3.
    result = match(r"^[0-9\.]+$", value)
    if !isnothing(result)
        l = length(value)
        return '.' in value ? parse(Float64, value) : parse(Int, value), l
    end
    # Now check if it's a hex or binary value (#x0f or #b01, for example)
    result = match(r"^\#(x|b)[0-9a-f]+$", value)
    if !isnothing(result)
        value = "0"*value[2:end]
        l = length(value)
        return value[2] == 'x' ? parse(Int, value[3:end], base=16) : parse(Int, value[3:end], base=2), l
    end
    
    # we get here if it's a variable
    return nothing, 0
end

function split_arguments(arguments::AbstractString)
    # Given a list like "* 2.0 1 (- 1.0) 3.0 (- 2.0)", return
    # :*, [2.0, 1, (:-, [1.0]), 3.0, (:-, [2.0])]

    result = match(r"^(\S+)\s", arguments)
    if isnothing(result)
        @error "Unable to retrieve operator from $arguments"
        return "", []
    end
    op = result.captures[1]
    ptr = result.offsets[1] + length(op)
    args = Any[]

    while ptr <= length(arguments)
        subs = lstrip(arguments[ptr:end]) # strip leading whitespace
        ptr += length(arguments[ptr:end]) - length(subs) # the difference

        @debug "looking in $(subs)"
        if startswith(subs, "(")
            tmp = __split_statements(subs)[1] # now we have the inside of (...)
            arg = split_arguments(tmp)
            ptr += length(tmp)+2 #$ the + 2 is for ()

        else
            tmp = split(subs, ' ', limit=2, keepempty=false)[1]
            arg, l = parse_return_root_values(tmp)
            ptr += l#:length(tmp)
            
        end
        if isnothing(arg) # give up, this expression is symbolic, eg + a b
            @debug "expr is symbolic, don't need to read it"
            return nothing
        end
        push!(args, arg)
    end
    @debug "returning $op, $args"
    return Symbol(op), args
end

evaluate_values(values::Number) = values

function evaluate_values(values_nested)
    op, values = values_nested
    values = map( (v) -> isa(v, Number) ? v : evaluate_values(v), values)
    return eval(op)(values...)
end

function parse_smt_statement(input::AbstractString)
    @debug "parsing $input"
    # this regex matches expressions like define-fun name () Type|(_ Type ...) (something)|integer|float
    # that is, the start and end () must be stripped
    matcher = r"^define-fun\s+([a-zA-Z0-9_]+)\s\(\)\s+([a-zA-Z]+|\(.*\))\s+(true|false|[a-f0-9\.\#x]+|\(.*\))$"
    result = match(matcher, input)
    if isnothing(result) || any(isnothing.(result.captures))
        @debug "Unable to read \"$input\""
        return nothing, nothing, nothing
    end
    # now we know we have all three, the first is the name, the second is the type, the third is the value
    (name, type, value) = result.captures
    
    type = parse_type(type)

    if startswith(value, "(")
        value = split_arguments(__split_statements(value)[1])
        value = isnothing(value) ? value : evaluate_values(value)
    else
        value, _ = parse_return_root_values(value)
    end
    
    return name, type, isnothing(value) ? value : type(value)
end