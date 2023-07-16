##### CONSTANTS FOR USE IN THIS FILE #####
# Dictionary of opnames with n>=2 operands. This is necessary because not all opnames are valid symbols
# For example, iff is = and := is an invalid symbol.
__smt_n_opnames = Dict(
    :AND     => "and",
    :OR      => "or",
    :XOR     => "xor",
    :IMPLIES => "=>",
    :IFF     => "=",
    :ITE     => "ite",
    :LT      => "<",
    :LEQ     => "<=",
    :GT      => ">",
    :GEQ     => ">=",
    :EQ      => "=",
    :ADD     => "+",
    :SUB     => "-",
    :MUL     => "*",
    :DIV     => "/",
)

__commutative_ops = [:AND, :OR, :XOR, :IFF, :EQ, :ADD, :MUL]

# Dictionary of opnames with 1 operand.
__smt_1_opnames = Dict(
    :NOT     => "not",
    :NEG     => "neg",
)

__boolean_ops = [:AND, :OR, :XOR, :IMPLIES, :IFF, :ITE, :LT, :LEQ, :GT, :GEQ, :EQ, :NOT]
