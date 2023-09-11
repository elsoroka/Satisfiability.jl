# Run this file after the other two benchmarks. It reads saved data from them.

using Pkg
Pkg.add("Plots")
Pkg.add("CSV")
using Plots, CSV

graph_infile = CSV.File(open("linecount_time_graph.txt", "r"), header=true)
pigeon_infile = CSV.File(open("linecount_time_pigeon.txt", "r"), header=true)

plot(graph_infile[:linecount], graph_infile[:seconds], label="Graph benchmark", marker=:square, color=:red,
     xaxis=:log, yaxis=:log, xlabel="Script length (# SMT-LIB commands)", ylabel="Time to generate script (seconds)")
plot!(pigeon_infile[:linecount], pigeon_infile[:seconds], label="Pigeon benchmark", marker=:o, color=:blue)

savefig("file_generation.pdf")