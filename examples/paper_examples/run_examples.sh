#! /bin/bash

echo "Pigeons benchmark"
julia pigeons_benchmark.jl

echo "Graph coloring benchmark"
julia graph_coloring_benchmark.jl

echo "File generation time plot"
julia plot_file_generation_time.jl

