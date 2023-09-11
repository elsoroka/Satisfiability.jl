#! /bin/bash
echo "Unit testing Satisfiability.jl"
julia ../../test/runtests.jl

echo "Pigeons benchmark"
julia pigeons_benchmark.jl

echo "Graph coloring benchmark"
julia graph_coloring_benchmark.jl

echo "File generation time plot"
julia plot_file_generation_time.jl

mkdir results
mv graph*.txt results/
mv pigeons*.txt results/
mv *.pdf results/
cp -r graph_genfiles results/graph_genfiles
cp -r pigeons_genfiles results/pigeons_genfiles
echo "Done, please run \"docker cp\" to retrieve the results."