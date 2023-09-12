#! /bin/bash
n=${1:-0}
size1=$((11 + $n))
echo "Pigeons benchmark of size $size1"
julia pigeons_benchmark.jl -n $size1

size2=$((12 + $n))
echo "Graph coloring benchmark of size $size2"
julia graph_coloring_benchmark.jl -n $size2

echo "File generation time plot"
julia plot_file_generation_time.jl

mkdir results
mv graph*.txt results/
mv pigeons*.txt results/
mv *.pdf results/
cp -r graph_genfiles results/graph_genfiles
cp -r pigeons_genfiles results/pigeons_genfiles
echo "Done, please run \"docker cp\" to retrieve the results."