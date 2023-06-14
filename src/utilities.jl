" flatten reshapes arrays of arbitrary # dimensions to 1D arrays."
flatten(a::Array{T}) where T = reshape(a, length(a))


"Flatten nested arrays to a single expression using operator to combine them.
For example, [z1, [z2, z3], z4] with operator and returns and(z1, and(z2, z3), z4).
This is a helper function designed to be called by save! or sat!"
function flatten_nested_exprs(operator, zs::Vararg{Union{Array{T}, T}}) where T <: BoolExpr
    # Combine the array exprs so we don't have arrays in arrays
    zs = map( (z) -> typeof(z) == BoolExpr ? z : operator(z), zs)
    return and(collect(zs)) # collect turns it from a tuple to an array
end


"is_permutation(a::Array, b::Array) returns True if a is a permutation of b.
is_permutation([1,2,3], [3,2,1]) == true
is_permutation([1,2,3], [1,3]) == false"
function is_permutation(a::Array, b::Array)
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

"Utility function for parsing SMT output. Split lines based on parentheses"
function split_line(output, ptr)
    stack = 0
    while ptr < length(output)
        lp = findnext("(", output, ptr)
        rp = findnext(")", output, ptr)
        if isnothing(lp) || isnothing(rp)
            return nothing
        end
        lp, rp = lp[1], rp[1]
        if lp < rp
            ptr = lp+1 # move past the next (
            stack += 1
        else
            ptr = rp+1 # move past the next )
            stack -= 1
        end
        if stack == 0
            return ptr
        end
    end
end


"Utility function for parsing SMT output. Read lines of the form '(define-fun x () Bool true)'
and extract the name (x) and the value (true)."
function read_line!(line, values)
    line = join(filter( (c) -> c != '\n', line),"")
    line = split(line[1:end-1], " ") # strip ( and )
    name = line[4] # TODO fix
    if line[end] == "true"
        values[name] = true
    elseif line[end] == "false"
        values[name] = false
    end
end

"Utility function for parsing SMT output. Takes output of (get-model) and returns a dict of values like {'x' => true, 'y' => false}.
If a variable is not set to true or false by get-model, it will not appear in the dictionary keys."
function parse_smt_output(output::String)
    values = Dict{String, Bool}()
    # there's one line with just (
    ptr = findnext("(\n", output, 1)[2] # skip it
    # lines 3 - n-1 are the model definitions
    next_ptr = ptr
    
    while ptr < length(output)
        next_ptr = split_line(output, ptr)
        if isnothing(next_ptr)
            break
        end
        #println(output[ptr:next_ptr])
        read_line!(output[ptr:next_ptr], values)
        ptr = next_ptr
    end
    # line n is the closing )
    return values
end