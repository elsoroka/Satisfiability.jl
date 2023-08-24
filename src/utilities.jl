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
"""
    output = "(
    (define-fun x () Bool true)
    (define-fun y () Bool false)
    (define-fun f ((x!0 Bool)) Bool (ite (= x!0 false) true false))"
    dict = parse_model(output)

Parse the SMT-LIB-formatted output of `(get-model)`, returning a Dict of names and values.
Values will be of the correct type; thus, in the example `dict["x"]` will be `true`.
Uninterpreted function values will be Julia functions themselves, thus `dict["f"]` is a function that accepts a Bool and returns a Bool.

This function is primarily useful when working with `InteractiveSolver`s.
"""
function parse_model(original_output::AbstractString)
    assignments = Dict()
    # recall the whole output will be surrounded by ()
    #output = __split_statements(original_output)
    output = split_items(original_output)
    if length(output) > 1 # something is wrong!
        @error "Unable to parse output\n\"$original_output\""
        return assignments
    end
    output = output[1]

    # now we've cleared the outer (), so iterating will go over each line in the model
    # first let's check if this output is a solver error
    if isa(output, String) # this means something went wrong, we got (error ...)
        @error "Solver error:\n$output"
        return assignments
    end

    for line in output
        if line[1] == Symbol("define-fun")
            @debug "parsing $line"
            name = String(line[2])
            # a function with no input arguments, since the syntax is define-fun name () ...
            if length(line[3]) == 0
                assignments[name] = evaluate_values(line[end])
            # a function with input arguments, thus we know it is an uninterpreted function because our code doesn't generate other kinds
            else
                assignments[name] = construct_function(line[end])
            end
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
function parse_value(value::AbstractString; skip_symbols=true)
    if value == "true"
        return true
    elseif value == "false"
        return false
    end
    # First check if it's a simple number, eg 1 or 2.3.
    result = match(r"^[0-9\.]+$", value)
    if !isnothing(result)
        return '.' in value ? parse(Float64, value) : parse(Int, value)
    end
    # Now check if it's a hex or binary value (#x0f or #b01, for example)
    result = match(r"^\#(x|b)[0-9a-f]+$", value)
    if !isnothing(result)
        l = length(value)
        return value[2] == 'x' ? parse(Int, value[3:end], base=16) : parse(Int, value[3:end], base=2)
    end
    
    # we get here if it's a variable
    return skip_symbols ? missing : Symbol(value)
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
    args = split_items(arguments, ptr)
    @debug "returning $op, $args"
    return [Symbol(op), args...]
end

function split_items(arguments::AbstractString, ptr=1)
    args = Any[]
    while ptr <= length(arguments)
        subs = lstrip(arguments[ptr:end]) # strip leading whitespace
        ptr += length(arguments[ptr:end]) - length(subs) # the difference
        if ptr > length(arguments)
            break
        end
        if startswith(subs, "(")
            tmp = __split_statements(subs)[1] # now we have the inside of (...)
            ptr += length(tmp)+2 #$ the + 2 is for ()
            arg = split_items(tmp)
        else
            arg = split(subs, (' ', '\n', '\r'), limit=2, keepempty=false)[1]
            ptr += length(arg)
            arg = parse_value(arg, skip_symbols=false)
        end
        push!(args, arg)
    end
    return args
end

evaluate_values(values::Number) = values

function evaluate_values(values_nested)
    op, values = values_nested[1], values_nested[2:end]
    @debug "evaluating $op on $values"
    if !any(isa.(values, Symbol))
        values = map( (v) -> isa(v, Number) ? v : evaluate_values(v), values)
        if !any(isnothing.(values))
            return op in keys(__smt_output_funcs) ? __smt_output_funcs[op](values...) : eval(op)(values...)
        end
    end
    return nothing
end

function construct_function(spec)
    if isa(spec, Number) # constant function
        return (x) -> spec
    else
        op = spec[1] ∈ keys(__smt_output_funcs) ? __smt_output_funcs[spec[1]] : eval(spec[1])
        return (x) -> op(map((s) -> isa(s, Symbol) ? x : construct_function(s)(x), spec[2:end])...)
    end
end

# some functions we might encounter in solver output
__smt_output_funcs = Dict(
    :to_real => (a::Int) -> Float64(Int),
    :to_int => (a::Float64) -> Integer(floor(a)),
    :as => (a, type) -> type == :Int ? Integer(floor(a)) : eval(type)(a),
    :(=) => (a,b) -> a == b,
)