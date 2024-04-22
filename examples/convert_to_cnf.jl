# In this example we convert a formula to CNF using Z3.
# This is sort of a trick because we have to send direct SMT-LIB commands to Z3 and parse the output.
# We also use Julia's metaprogramming capabilities. Again, this example is just for fun!

using Satisfiability

@satvariable(z[1:5], Bool)

expr = and(or(z[3], not(z[1]), or(z[5], z[4])), or(z[2], and(z[5], z[4]), z[3], not(z[5]), z[1]))

solver = open(Z3())
assert!(solver, expr)

# The magic sauce: this command tells Z3 to simplify your expression to CNF (conjunctive normal form).
cmd = "(apply (then (! simplify :elim-and true) elim-term-ite tseitin-cnf))"

# We expect a response that looks like
#=
 (goals
   (goal
     (or z_5 z_4 (not z_1) z_3)
     :precision precise :depth 3)
   )
 )
 =#
# so to obtain the whole response we use the nested_parens_match function.
response = send_command(solver, cmd, is_done=nested_parens_match)
println("Got response:\n$response")

# Now we have to parse it.
parsed = Satisfiability.split_items(response)

# this gives us a nested array set beginning with [:goals [:goal [:or :z_5 :z_4 [:not :z_1] :z_3] ...]]
parsed_exprs = []
for item in parsed[1][2] # skip the first two levels
    if isa(item, Array)
        push!(parsed_exprs, item)
    end
end

# Now since we defined the individual variables z_1,...,z_5 we can use metaprogramming
# to construct Julia Expr objects and eval() them, yielding a Satisfiability formula in CNF form.
# This works because the syntax to make an Expr like or(z_1, z_2) is Expr(:call, :or, :z1, :z2)

function make_expr(raw::Symbol)
    result = split(String(raw), "_") # if raw is a variable symbol like z_i that corresponds to an index
    # we rewrite it as z[i] because that will be in scope.
    if length(result) == 1 # we didn't split
        return raw
    elseif length(result) == 2
        return Expr(:ref, Symbol(result[1]), parse(Int, result[2]))
    end
  end

  make_expr(raw::Array) = Expr(:call, make_expr.(raw)...)

exprs = make_expr.(parsed_exprs)
formula = and(eval.(exprs))
println("Result:\n$formula")
