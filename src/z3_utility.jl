# utility functions and definitions

import Z3
import Z3.ExprAllocated    as _Z3Expr
import Z3.ContextAllocated as _Z3Context
import Z3.SolverAllocated  as _Z3Solver
# https://github.com/ahumenberger/Z3.jl
import Base.~, Base.length, Base.size, Base.show, Base.string

# this is wh we have to wrap the Convex.jl type which would overwise be fine 
# https://github.com/JuliaLang/julia/issues/5

# Reasoning: We call this BoolExpr instead of BoolVar
# because a BoolVar can be an expression on its own
# and it is too confusing otherwise to define things like &, ~, etc
# with two separate types
#= Desired behavior
z is a BoolExpr of dim 1 with no children and operation :Identity
	it is an expression on its own
	when we initialize! it, its Array{Z3Expr} will be a one-element array of bool_val
zn is a BoolExpr of dim n with no children and operation :Identity
	when we initialize! it, its Array{Z3Expr} will be n bool_val elements
z1n ∧ z2n is a BoolExpr of dim n with two children, z1n and z2n and operation :And
	when we initialize! it, its Array{Z3Expr} will be n elements z1n[i] ∧ z2n[i]

we want to operate on both initialize!'ed and non-initialized variables
if z1n and z2n are not initialized
	we expect its Array{Z3Expr} to be empty
	so when we do z1n .∧ z2n
	we want n expressions
=#

# BoolExpr is array-like but does not subtype AbstractArray
# WHY NOT SUBTYPE ABSTRACTARRAY:
#	because it doesn't make sense to implement getindex
# WHY NOT MAKE ARRAYS OF 1-element BoolExpr:
#	it breaks the knowledge that a Z3.bool_val belongs to a bool vector
# For example, it interferes with our ability to initialize! a vector-valued z3 variable sensibly
# e.g. you have z1 of size n, z2 of size (n,m) and you initialize!(z1 ∨ z2) (which is size (n,m))
#      you want to initialize! z1's Z3.bool_val's with a sensible naming scheme like z1_1,...,z1_n
#      because you're operating over an nxm array of z1[i] ∨ z2[i,j] you can't distinguish, from within the loop,
#      between an array of size n and an array of size (n,m)
#      so you'd end up naming z1_1_1,...,z1_n_1.
#      this is itself not so bad but suggests a bad code architecture! Augh.
abstract type AbstractExpr end

mutable struct BoolExpr <: AbstractExpr
	op       :: Symbol
	children :: Array{AbstractExpr}
	name     :: String
	shape    :: Tuple{Vararg{Integer}}
	# z3_expr is the same shape as children
	z3_expr  :: Array{_Z3Expr}
	# iff context is unitialized, z3_expr is empty
	context  :: Union{Nothing, _Z3Context}
	value    :: Union{Nothing, Bool, Array{Bool}}
end

BoolExpr(n::Int, name::String)         = BoolExpr(:Identity, Array{BoolExpr}[], name, (n,), Array{_Z3Expr}[], nothing, nothing)
BoolExpr(m::Int, n::Int, name::String) = BoolExpr(:Identity, Array{BoolExpr}[], name, (m,n), Array{_Z3Expr}[], nothing, nothing)
BoolExpr(name::String)                 = BoolExpr(1, name)
#=
We are Doing A Bad Thing here and making a tree-like data structure (BoolExpr) behave like an array!
Bad Things are often more performant, except when they aren't.
It is our hope the first case will happen here.
=#
# some more utilities
squeeze(shape::Tuple) = Tuple([s for s in shape if s > 1])
# Check if two shapes are broadcastable
# TODO ASAP this is a bug
is_broadcastable(shape1::Tuple, shape2::Tuple) =
	all([dim1 == dim2 || dim1 == 1 || dim2 == 1 for (dim1, dim2) in zip(shape1, shape2)])
# Compute the size of a broadcasted list of shapes
function broadcast_size(shapes::Array)
	l_max = maximum([length(s) for s in shapes])
	sizes = fill(1, length(shapes), l_max)
	# pad all tuples with ones
	for (i,s) in enumerate(shapes)
		sizes[i,1:length(s)] .= s
	end
   return Tuple([maximum(sizes[:,i]) for i=1:l_max])
end

f(a...) = [a...]
broadcast_collect(exprs::Array{T}) where T <: Array = f.(exprs...)

# https://docs.julialang.org/en/v1/manual/interfaces/#man-interface-array
Base.size(e::AbstractExpr) = e.shape
Base.length(e::AbstractExpr) = prod(size(e))

function getindex(e::BoolExpr, idx::Int)
	if isnothing(e.context)
		return BoolExpr(e.op, [child[idx] for child in e.children], (1,), Array{_Z3Expr}[], nothing, nothing)
	else
		return BoolExpr(e.op, [child[idx] for child in e.children], (1,), e.z3_expr[idx], e.context, nothing)
	end
end
function getindex(e::BoolExpr, idx1::Int, idx2::Int)
	if isnothing(e.context)
		return BoolExpr(e.op, [child[idx1, idx2] for child in e.children], (1,), Array{_Z3Expr}[], nothing, nothing)
	else
		return BoolExpr(e.op, [child[idx1, idx2] for child in e.children], (1,), e.z3_expr[idx1, idx2], e.context, nothing)
	end
end


# optional methods
# TODO 1 Define the iterator
#=
function iterate(e::BoolExpr, i=0)
	if i <= length(e.children)
		return e.children[i], i+1
	else
		return nothing
	end
end
=#

# Desired  behavior:
#=
	We want to be able to broadcast Z3Exprs, at least, avoiding the mistake of Convex.jl which does not support the dot
	So for example, if a = Var(n, :Bool) and b = Var(n,m,:Bool) then a .∧ b produces the array:
	a1 ∧ b11, a1 ∧ b12 ... a1 ∧ b1m
	a2 ∧ b21 ...           a2 ∧ b2m
	⋮
	an ∧ bn1 ...           an ∧ bnm

	# What does (a.∨ b) .∧ c produce??? where c is size n
	(a1 ∨ b11) ∧ c1, (a1 ∨ b12) ∧ c1 ... (a1 ∨ b1m) ∧ c1
	(a2 ∨ b21) ∧ c2 ...                  (a2 ∨ b2m) ∧ c2
	⋮
	(an ∨ bn1) ∧ cn ...                  (an ∨ bnm) ∧ cn
	
	# Of course we won't do such things regularly but it will be good to have them work.
=#

### EXPRESSION ###
# An expression is built from variables

# To combine n variables, use these functions
function and(zs::Array{T}) where T <: AbstractExpr
	# and of one z (or zero?) is z
	if length(zs) < 2
		return length(zs) == 1 ? zs[1] : nothing
	end

	for i=1:length(zs)-1
		if !is_broadcastable(size(zs[i]), size(zs[i+1]))
			throw(DimensionMismatch("Unable to & variables of shapes $(size(zs[i])) and $(size(zs[i+1]))"))
		end
		if zs[i].context != zs[i+1].context
			error("Unable to & variables with different contexts")
		end
	end
	name = "and_$(zs[1].name)...$(zs[end].name)"
	output_shape = broadcast_size([size(zi) for zi in zs])
	if isnothing(zs[1].context)
		return BoolExpr(:And, zs, name, output_shape, Array{_Z3Expr}[], nothing, nothing)
	else
		return BoolExpr(:And, zs, name, output_shape, [Z3.and(reduce(hcat, [zi.z3_expr for zi in zs])),], zs[1].context, nothing)
	end
end

function or(zs::Array{T}) where T <: AbstractExpr
	# and of one z (or zero?) is z
	if length(zs) < 2
		return length(zs) == 1 ? zs[1] : nothing
	end

	for i=1:length(zs)-1
		if !is_broadcastable(size(zs[i]), size(zs[i+1]))
			throw(DimensionMismatch("Unable to | variables of shapes $(size(zs[i].shape)) and $(size(zs[i+1].shape))"))
		end
		if zs[i].context != zs[i+1].context
			error("Unable to | variables with different contexts")
		end
	end
	name = "or_$(zs[1].name)...$(zs[end].name)"
	output_shape = broadcast_size([size(zi) for zi in zs])
	if isnothing(zs[1].context)
		return BoolExpr(:Or, zs, name, output_shape, Array{_Z3Expr}[], nothing, nothing)
	else
		return BoolExpr(:Or, zs, name, output_shape, [Z3.or(reduce(hcat,[zi.z3_expr for zi in zs])),], zs[1].context, nothing)
	end
end

# Here are more expressions
~(z::BoolExpr) = BoolExpr(:Not, [z,], "~$(z.name)", z.shape, z.z3_expr, z.context, nothing)
∧(z1::AbstractExpr, z2::AbstractExpr) = and([z1, z2])
∨(z1::AbstractExpr, z2::AbstractExpr) = or([z1, z2])
⟹(z1::BoolExpr, z2::AbstractExpr) = or([(~z1), z2])


# Initializing z3 expressions (helper)
function _z3_allocate(context::_Z3Context, shape::Tuple, name)
	if length(shape) == 1
		return [Z3.bool_const(context, "$(name)_$i") for i=1:shape[1]]
	elseif length(shape) == 2
		result = Array{_Z3Expr}(undef, shape)
		for i=1:shape[1]
			for j=1:shape[2]
				result[i,j] = Z3.bool_const(context, "$(name)_$(i)_$j")
			end
		end
		return result
	else
		throw(DimensionMismatch("Expression has unsupported size $(shape)"))
	end
end

function _z3_initialize!(expr::BoolExpr, context::_Z3Context, depth=1)
	# Base case
	if expr.op == :Identity
		expr.context = context
		expr.z3_expr = _z3_allocate(context, expr.shape, expr.name)
	# Recursive case
	else
		for e in expr.children
			_z3_initialize!(e, context, depth+1)
		end
		expr.context = context
		_z3_construct_expr!(expr)
	end
end

# TODO 3 this is getting complicated, write a unittest file.

function _z3_construct_expr!(expr::BoolExpr)
	if expr.op == :And
		# The line ((e::BoolExpr) -> e.z3_expr).(expr.children)
		# is the (possibly) more efficient version of [e.z3_expr for e in expr.children]
		expr.z3_expr = map(Z3.and, broadcast_collect( ((e::BoolExpr) -> e.z3_expr).(expr.children)) )
	elseif expr.op == :Or
		expr.z3_expr = map(Z3.or, broadcast_collect( ((e::BoolExpr) -> e.z3_expr).(expr.children)) )
	elseif expr.op == :Not
		# by construction there is only one child since it's a unary operator
		expr.z3_expr = map(Z3.not, expr.children[1].z3_expr)
	else
		error("Unrecognized operation $(expr.op)")
	end
end

# This is the one we actually call
initialize!(expr::BoolExpr) = _z3_initialize!(expr, Z3.Context())


# Printing behavior
# https://docs.julialang.org/en/v1/base/io-network/#Base.print
Base.show(io::IO, expr::BoolExpr) = print(io, string(expr))
function Base.string(expr::BoolExpr, indent=0)
	if expr.op == :Identity	
		return "$(repeat(" | ", indent))$(expr.name) $(expr.shape)$(!isnothing(expr.context) ? ": $(expr.z3_expr) = $(expr.value)" : "")\n"
	else
		res = "$(repeat(" | ", indent))$(expr.op)\n"
		for e in expr.children
			res *= string(e, indent+1)
		end
		return res
	end
end

# Solving the problem
#=
s = Z3.Solver(_ctx)
add(s, problem._constraint_predicates)
add(s, problem.predicates)
status = check(s)
=#
mutable struct Problem
	predicates :: Array{BoolExpr}
	context    ::_Z3Context
	solver     ::_Z3Solver
	status     :: Symbol # in order of happiness, :SAT, :UNSAT, :UNKNOWN
end

function Problem(predicates::Array{BoolExpr})
	# We want to initialize the Z3Context and solver
	context = Z3.Context()
	map((pred) -> _z3_initialize!(pred, context), predicates)
	return Problem(predicates, context, Z3.Solver(context), :UNSAT)
end
Problem(predicate::BoolExpr) = Problem([predicate,])

function solve!(p::Problem)
	if isnothing(p.context)
		println("Warning: Problem should always have initialized internal Z3 context.")
		context = Z3.Context()
		_z3_initialize!.(p.predicates, context)
		p.context = context # this is deliberately last so it cannot be set if _z3_initialize! somehow crashes
	end
	# this comes about because we have an array of BoolExprs
	# but internally each BoolExpr has a list of Z3Exprs
	# because we are covering a single-variable C++ wrapper API in a vector interface
	p.solver = Z3.Solver(p.context)
	Z3.reset(p.solver)
	for expr in p.predicates
		map((pred) -> Z3.add(p.solver, pred), expr.z3_expr)
	end
	status = Z3.check(p.solver)
	# https://github.com/Z3Prover/z3/blob/master/src/api/julia/z3jl.cpp#L359
	# statuses are 0, 1, 2
	if status == Z3.sat
		p.status = :SAT
		# pull values out of z3 (there seems to be no better way to do this?)
		m = Z3.get_model(p.solver)
		assignment = Dict{String, Bool}()
		for (k, v) in Z3.consts(m)
			#println("$k = $v")
	    	assignment[string(k)] = (string(v) == "true")
		end
		map((pred) -> assign!(pred, assignment), p.predicates)
	elseif status == Z3.unsat
		p.status == :UNSAT
	else
		p.status == :UNKNOWN
	end

end

# Given an assignment, traverse the BoolExpr to assign values
function assign!(expr::BoolExpr, assignment::Dict{String, Bool})
	# base case
	if expr.op == :Identity
		# a 1D array
		if length(expr.shape) == 1
					expr.value = Array{Bool}(undef, expr.shape[1])
			expr.value .= [assignment["$(expr.name)_$i"] for i=1:expr.shape[1]]
		# a 2D array
		else
			expr.value = Array{Bool}(undef, expr.shape[1], expr.shape[2])
			for i=1:expr.shape[1]
				expr.value[i,:] .= [assignment["$(expr.name)_$(i)_$j"] for j=1:expr.shape[2]]
			end
		end
	end

	# recursive case!
	for e in expr.children
		assign!(e, assignment)
	end
	# TODO assign values here too but too lazy rn
end

#=
# SELF TEST
z1 = BoolExpr(2, "z1")
z2 = BoolExpr(2,3, "z2")

expr = (z1∧z2)⟹z1
println(expr)
initialize!(expr)

prob = Problem(expr)
solve!(prob)
println(z1.value)
println(z2.value)

z1 = BoolExpr(1, "z1")
z2 = BoolExpr(1, "z2")

predicates = [z1 ∨ z2, ~z1 ∨ z2, ~z1 ∨ ~z2]
prob = Problem(predicates)
solve!(prob)

println(prob.status)
println("z1 = $(z1.value)")
println("z2 = $(z2.value)")
=#