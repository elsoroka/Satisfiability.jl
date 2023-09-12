# Run this file after the other two benchmarks. It reads saved data from them.

using Pkg
Pkg.add("CSV")
using CSV

graph_infile = CSV.File(open("linecount_time_graph.txt", "r"), header=true)
pigeon_infile = CSV.File(open("linecount_time_pigeon.txt", "r"), header=true)
lg = length(graph_infile[:seconds])
lp = length(pigeon_infile[:seconds])

outfile = open("filesize.txt", "w")
write(outfile, "nlines_pigeon\ttime_pigeon\tnlines_graph\ttime_graph\n")
for i=1:max(lg, lp)
     pigeon_i = i > lp ? "\t" : "$(pigeon_infile[:linecount][i])\t$(pigeon_infile[:seconds][i])"
     graph_i = i > lg ? "\t" : "$(graph_infile[:linecount][i])\t$(graph_infile[:seconds][i])"
     write(outfile, "$pigeon_i\t$graph_i\n")
end
close(outfile)