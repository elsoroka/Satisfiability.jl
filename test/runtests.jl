push!(LOAD_PATH, "../../src")
push!(LOAD_PATH, "./")

using Logging
using Satisfiability
using TestItemRunner

normalize_endings(s::String) = replace(s, "\r\n" => "\n")
Base.isapprox(str1::String, str2::String) = normalize_endings(str1) == normalize_endings(str2)

SET_DUPLICATE_NAME_WARNING!(false)
CLEAR_VARNAMES!()

if get(ENV, "GPU_TESTS", "") != "true"
    println("skipping gpu tests (set GPU_TESTS=true to test gpu)")
end

# filter for the test
testfilter = ti -> begin
  exclude = Symbol[]
  if get(ENV,"JET_TEST","")!="true"
    push!(exclude, :jet)
  end
  if !(VERSION >= v"1.10")
    push!(exclude, :doctests)
    push!(exclude, :aqua)
  end

  if get(ENV, "GPU_TESTS", "")!="true"
    push!(exclude, :gpu)
  end

  if !(Base.Sys.islinux() & (Int===Int64))
    push!(exclude, :bitpack)
  end

  return all(!in(exclude), ti.tags)
end

println("Starting tests with $(Threads.nthreads()) threads out of `Sys.CPU_THREADS = $(Sys.CPU_THREADS)`...")

@run_package_tests filter=testfilter
