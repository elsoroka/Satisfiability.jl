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
function __split_statements(input::String)
    statements = String[]
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
                @warn "( at character $ptr without matching )"
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

# Given a line like "define-fun X () Bool|Int|Real (op x1 x2 ...)"
# skip it
# Given a line like "define-fun X () Bool|Int|Real value|(- value)"
# where value is true|false|int|float, return the name X and the value
function __parse_line(line::String)
    original_line = deepcopy(line)
    # filter ' ' and '\n'
    line = filter((c) -> c != ' ' && c != '\n', line)
    ptr = 10 # line always starts with define-fun so we can skip that
    name = line[ptr+1:findnext('(', line, ptr+1)-1]
    ptr += length(name)
    ptr = findnext(')', line, ptr+1) # skip the next part ()
    # figure out what the return type is
    return_type = nothing
    
    #@debug "line = $(line[ptr+1:end])"
    if startswith(line[ptr+1:end], "Bool")
        return_type = Bool
        ptr += 4
    elseif startswith(line[ptr+1:end], "Int")
        return_type = Int64
        ptr += 3
    elseif startswith(line[ptr+1:end], "Real")
        return_type = Float64
        ptr += 4
    elseif startswith(line[ptr+1:end], "(_BitVec")
        tmp_ptr = ptr + length("(_BitVec")
        ptr = findnext(')', line, tmp_ptr+1) # move past the type declaration (_ BitVec [0-9]+)
        return_type = nextsize(parse(Int, line[tmp_ptr+1:ptr-1])) # this figures out the unsigned int type of the SMT-LIB BitVec size
    else
        @error "Unable to parse return type of \"$original_line\""
    end
    try
        value = __parse_value(return_type, line[ptr+1:end])
        return name, value # value may be nothing if it's a function and not a variable
    catch
        @error "Unable to parse value of type $return_type in \"$original_line\""
        rethrow()
    end
end

# Determine whether line represents the value of a variable (ex: "0", "true", "(- 2)")
# or a constructed function (ex: "(+ 1 a)", "(+ 2 a b"), "(>= (+ 1 a) b)")
# Return nothing if it's a function and the value if it's a variable
function __parse_value(value_type::Type, line::String)
    l = findfirst('(', line)
    if !isnothing(l) # there is a parenthesis
        # the only valid thing to see here is -
        if line[l+1] != '-'
            # now we know it's a function and not a variable
            return nothing
        end
        # trim the ()
        line = line[l+1:findlast(')', line)-1]
    end
    if value_type <: Unsigned || value_type <: BigInt # these both correspond to BitVectors
        # the dumb thing here is Z3 returns them with the syntax #x0f instead of 0x0f
        line = "0"*line[2:end]
    end
    return parse(value_type, line)
end

function parse_smt_output(original_output::String)
    #println(output)
    assignments = Dict()
    # recall the whole output will be surrounded by ()
    output = __split_statements(original_output)
    if length(output) > 1 # something is wrong!
        @error "Unable to parse output\n\"$original_output\""
        return assignments
    end
    # now we've cleared the outer (), so iterating will go over each line in the model
    for line in __split_statements(output[1])
        (name, value) = __parse_line(line)
        if !isnothing(value)
            assignments[name] = value
        end
    end
    return assignments
end

# parse a string corresponding to an SMT-LIB type
function parse_type(type::String)
    if startswith(type, "(") # it's a fancy type like (_ BitVec 16)
        result = match(r"\(_\s([a-zA-Z]+)\s([0-9]+)\)", type)
        if any(isnothing.(result.captures))
            @error "Unable to parse SMT-LIB type \"$type\""
        end
        if result.captures[1] == "BitVec"
            return BitVectorExpr{nextsize(parse(Int, result.captures[2]))}
        end
        # we shouldn't get here
        @error "Unknown SMT-LIB type \"type\""
    else # simple type like "Bool" or "Real"
        types = Dict("Bool" => BoolExpr, "Int" => IntExpr, "Real" => RealExpr)
        return types[type]
    end
end

# parse a string corresponding to an SMT-LIB value, and if it has no variables, return the numeric value
function parse_return_root_values(value::String)
    # First check if it's a simple number, eg 1 or 2.3. This will also catch Booleans which is fine.
    result = match(r"^[0-9\.]+$", value)
    if !isnothing(result)
        return '.' in value ? parse(Float64, value) : parse(Int, value)
    end
    # Now check if it's a hex or binary value (#x0f or #b01, for example)
    result = match(r"^\#(x|b)[0-9a-f]+$", value)
    if !isnothing(result)
        value = "0"*value[2:end]
        return value[2] == 'x' ? parse(Int, value[3:end], base=16) : parse(Int, value[3:end], base=2)
    end
    # If we have failed twice, now we have to check for expressions
    # For example, (/ 2.0 3.0) or (- 1) are both valid
    result = match(r"^\((\S+)\s", value)
    if !isnothing(result)
        op = result.captures[1]
        # note that at this point arguments are not broken up, so they could be
        # for example, "a b" or "
        arguments = value[result.offsets[1]+length(result.captures[1])+1:end-1]
        # now arguments is the list of the arguments to op, with no leading space and no trailing )
        # arguments may be single things like #x0f, #b0011, 2.0 or 1
        # or they may be nested expressions like (- 1)
        ptr = 1
        split_args = []
        while ptr <= length(arguments)
            result = match(r"^(\(.+?\)+|[0-9\.]+|\#b[0-1]+|\#x[0-9a-f]+)(\s*)", arguments[ptr:end])
            #println("caught $result, \"$(arguments[ptr:end])\"")
            if isnothing(result)
                break
            end
            
            ptr += length(result.captures[1]) + result.offsets[1] - 1 + length(result.captures[2]) # +a to clear the space
            arg = result.captures[1]
            println("ptr = $ptr, arg=$arg")
            val = parse_return_root_values(String(arg))
            push!(split_args, val)
            #println("found $(split_args[end])")
        end
        return Symbol(op), split_args
    end
    
    # we should not get here
    @error("Unable to parse value \"$value\"")
end

evaluate_values(values::Number) = values

function evaluate_values(values_nested)
    op, values = values_nested
    values = map( (v) -> isa(v, Number) ? v : evaluate_values(v), values)
    return eval(op)(values...)
end

function parse_smt_statement(input::String)
    # this regex matches expressions like define-fun name () Type|(_ Type ...) (something)|integer|float
    # that is, the start and end () must be stripped
    matcher = r"^define-fun\s([a-zA-Z0-9_]+)\s\(\)\s([a-zA-Z]+|\(.*\))\s+([0-9\.]+|\(.*\))$"
    result = match(matcher, input)
    if any(isnothing.(result.captures))
        @error "Error parsing line \"$input\""
    end
    # now we know we have all three, the first is the name, the second is the type, the third is the value
    (name, type, value) = result.captures
    
    type = parse_type(type)
    value = evaluate_values(parse_return_root_values(value))
    return (name, type), value
end