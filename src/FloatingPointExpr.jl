import Base: +, -, *, /, ^, div, inv, mod, abs, ==, !=, promote_rule, convert

abstract type NumericExpr <: AbstractExpr end

# Global dictionary to track variable names for FloatingPointExpr
GLOBAL_VARNAMES = Dict{Type, Vector{String}}()
WARN_DUPLICATE_NAMES = true

# Mapping rounding mode
const ROUNDING_MODE_MAP = Dict(
    :RNE => :round_nearest_ties_to_even,
    :RNA => :round_nearest_ties_to_away,
    :RTP => :round_toward_positive,
    :RTN => :round_toward_negative,
    :RTZ => :round_toward_zero
)

"""
    FloatingPointExpr

Represents a floating-point expression with support for operations, precision, and rounding modes.

### Arguments:
- `op`: Symbol representing the operation (e.g., `:add`, `:mul`, etc.).
- `children`: Array of child expressions (inputs to the operation).
- `value`: The numerical value of the expression (can be `nothing` or `missing`).
- `name`: A unique name for the expression.
- `__is_commutative`: Boolean indicating whether the operation is commutative.
- `eb`: Exponent bit width.
- `sb`: Significand bit width (includes the hidden bit).
- `rounding_mode`: Symbol specifying the rounding mode.
"""
mutable struct FloatingPointExpr <: NumericExpr
    op                :: Symbol
    children          :: Vector{AbstractExpr}
    value             :: Union{Float64, Nothing, Missing}
    name              :: String
    __is_commutative  :: Bool
    eb                :: Int
    sb                :: Int
    rounding_mode     :: Symbol

    # for convenience
    FloatingPointExpr(op::Symbol, children::Vector{T},
                      value::Union{Float64, Nothing, Missing},
                      name::String, __is_commutative::Bool,
                      eb::Int, sb::Int, rounding_mode::Symbol) where T <: AbstractExpr = new(op, children, value, name, __is_commutative, eb, sb, rounding_mode)
end

"""
    FloatingPointExpr(name::String; eb=11, sb=53, rounding_mode=:RNE)

Create a new `FloatingPointExpr` instance with the given name, exponent bit width (`eb`), significand bit width (`sb`), and rounding mode.

### Arguments:
- `name::String`: A unique name for the expression.
- `eb::Int`: Exponent bit width (default is 11).
- `sb::Int`: Significand bit width (default is 53).
- `rounding_mode::Symbol`: Rounding mode used in the operation (default is `:RNE`).

```julia
expr = FloatingPointExpr("my_expr", eb=8, sb=24, rounding_mode=:RTP)
```
"""
function FloatingPointExpr(name::String; value::Union{Float64, Nothing, Missing}=nothing, eb::Int=11, sb::Int=53, rounding_mode::Symbol=:RNE)
    if haskey(ROUNDING_MODE_MAP, rounding_mode)
        rounding_mode = ROUNDING_MODE_MAP[rounding_mode]
    elseif !(rounding_mode in values(ROUNDING_MODE_MAP))
        throw(ArgumentError("Invalid rounding mode. See docstring for valid modes."))
    end

    # Ensure global variable tracking
    if !haskey(GLOBAL_VARNAMES, FloatingPointExpr)
        GLOBAL_VARNAMES[FloatingPointExpr] = String[]
    end

    if name in GLOBAL_VARNAMES[FloatingPointExpr]
        WARN_DUPLICATE_NAMES && @warn("Duplicate variable name: $name")
    else
        push!(GLOBAL_VARNAMES[FloatingPointExpr], name)
    end

    return FloatingPointExpr(:identity, AbstractExpr[], value, name, false, eb, sb, rounding_mode)
end

# Special FloatingPoint constants
"""
    fp_zero(eb::Int=11, sb::Int=53, sign::Bool=false)

Create a FloatingPointExpr representing zero, with optional sign (sign=true for negative zero).
"""
function fp_zero(eb::Int=11, sb::Int=53, sign::Bool=false)
    value = sign ? -0.0 : 0.0
    FloatingPointExpr(:zero, [], value, "zero", true, eb, sb, :round_nearest_ties_to_even)
end

"""
    fp_infinity(eb::Int=11, sb::Int=53, sign::Bool=false)

Create a FloatingPointExpr representing infinity, with optional sign (sign=true for negative infinity).
"""
function fp_infinity(eb::Int=11, sb::Int=53, sign::Bool=false)
    value = sign ? -Inf : Inf
    FloatingPointExpr(:infinity, [], value, "infinity", true, eb, sb, :round_nearest_ties_to_even)
end

"""
    fp_nan(eb::Int=11, sb::Int=53)

Create a FloatingPointExpr representing NaN (Not a Number).
"""
function fp_nan(eb::Int=11, sb::Int=53)
    FloatingPointExpr(:nan, [], NaN, "NaN", true, eb, sb, :round_nearest_ties_to_even)
end

# FloatingPoint literals
"""
    fp_literal(sign::Bool, exponent::Int, significand::Int, eb::Int, sb::Int)

Create a floating-point literal expression using the given components:
- `sign`: Boolean indicating the sign (false for positive, true for negative)
- `exponent`: The exponent part of the floating-point number
- `significand`: The significand (fractional) part of the floating-point number
- `eb`: The exponent bit width
- `sb`: The significand bit width

Returns a `FloatingPointExpr` representing the floating-point literal.
"""
function fp_literal(sign::Bool, exponent::Int, significand::Int, eb::Int, sb::Int)
    # Calculate the value using ldexp, considering sign, exponent, and significand
    value = if sign
        -ldexp(significand / (1 << (sb - 1)), exponent - (1 << (eb - 1)) + 1)
    else
        ldexp(significand / (1 << (sb - 1)), exponent - (1 << (eb - 1)) + 1)
    end
    # Construct and return a FloatingPointExpr using the correct constructor
    return FloatingPointExpr(:literal, AbstractExpr[], value, "literal", false, eb, sb, :round_nearest_ties_to_even)
end

function is_nan(fp::FloatingPointExpr)
    isnan(fp.value)
end

function is_infinite(fp::FloatingPointExpr)
    isinf(fp.value)
end

function is_zero(fp::FloatingPointExpr)
    fp.value == 0.0
end

function is_positive(fp::FloatingPointExpr)
    fp.value > 0.0
end

function is_negative(fp::FloatingPointExpr)
    fp.value < 0.0
end

# Arithmetic operations
Base.:+(fp1::FloatingPointExpr, fp2::FloatingPointExpr) = begin
    if !fp1.__is_commutative && fp2.__is_commutative
        fp1, fp2 = fp2, fp1
    end
    result = fp1.value + fp2.value
    rounded_result = round_float(result, fp1.rounding_mode)
    FloatingPointExpr(:add, [fp1, fp2], rounded_result, "add", true, fp1.eb, fp1.sb, fp1.rounding_mode)
end

Base.:*(fp1::FloatingPointExpr, fp2::FloatingPointExpr) = begin
    if !fp1.__is_commutative && fp2.__is_commutative
        fp1, fp2 = fp2, fp1
    end
    result = fp1.value * fp2.value
    rounded_result = round_float(result, fp1.rounding_mode)
    FloatingPointExpr(:mul, [fp1, fp2], rounded_result, "mul", true, fp1.eb, fp1.sb, fp1.rounding_mode)
end

Base.:-(fp1::FloatingPointExpr, fp2::FloatingPointExpr) = begin
    result = fp1.value - fp2.value
    rounded_result = round_float(result, fp1.rounding_mode)
    FloatingPointExpr(:sub, [fp1, fp2], rounded_result, "sub", false, fp1.eb, fp1.sb, fp1.rounding_mode)
end

Base.:/(fp1::FloatingPointExpr, fp2::FloatingPointExpr) = begin
    result = fp1.value / fp2.value
    rounded_result = round_float(result, fp1.rounding_mode)
    FloatingPointExpr(:div, [fp1, fp2], rounded_result, "div", false, fp1.eb, fp1.sb, fp1.rounding_mode)
end

# Fused Multiply-Add
function fp_fma(fp1::FloatingPointExpr, fp2::FloatingPointExpr, fp3::FloatingPointExpr)
    if !fp1.__is_commutative && fp2.__is_commutative
        fp1, fp2 = fp2, fp1
    end
    result = fp1.value * fp2.value + fp3.value
    rounded_result = round_float(result, fp1.rounding_mode)
    FloatingPointExpr(:fma, [fp1, fp2, fp3], rounded_result, "fma", false, fp1.eb, fp1.sb, fp1.rounding_mode)
end

function round_float(value::Float64, mode::Symbol)

    if mode == :round_nearest_ties_to_even
        return round(value)
    elseif mode == :round_toward_positive
        return ceil(value)
    elseif mode == :round_toward_negative
        return floor(value)
    elseif mode == :round_toward_zero
        return trunc(value)
    else
        throw(ArgumentError("Unsupported rounding mode: $mode"))
    end
end


Base.convert(::Type{FloatingPointExpr}, x::IntExpr) = begin
    val = isnothing(x.value) ? 0.0 : float(x.value)  # Default to 0.0 if value is `Nothing` or `Missing`s
    op = :identity
    children = AbstractExpr[]
    name = "convert_from_int_$(x.name)"
    eb = 11
    sb = 53
    rounding_mode = :round_nearest_ties_to_even
    return FloatingPointExpr(op, children, val, name, true, eb, sb, rounding_mode)
end

Base.convert(::Type{FloatingPointExpr}, x::RealExpr) = begin
    val = isnothing(x.value) ? 0.0 : x.value  # Default to 0.0 if value is `Nothing` or `Missing`
    op = :identity
    children = AbstractExpr[]
    name = "convert_from_real_$(x.name)"
    eb = 11
    sb = 53
    rounding_mode = :round_nearest_ties_to_even  # Default rounding mode
    return FloatingPointExpr(op, children, val, name, true, eb, sb, rounding_mode)
end
