@testitem "README.md exampes" begin

    using Satisfiability

    function test_julia_examples_in_markdown(path)
        file = read(path, String)
        file_by_code_blocks = split(file, "```julia")[2:end]
        possible_examples = map(s -> first(split(s, "```")), file_by_code_blocks)
        for example ∈ possible_examples
            quote_example = "begin\n" * example * "\nend"
            parsed = @test_nowarn Meta.parse(quote_example)
            @test try
                eval(parsed)
                true
            catch e
                showerror(stderr, e, catch_backtrace())
                println()
                false
            end
        end
    end

    @testset "Test README.md examples" begin
        # Suppress printouts since this only tests that the examples in the README run.
        std_ = stdout
        redirect_stdout(devnull)
        test_julia_examples_in_markdown("../README.md")
        redirect_stdout(std_)
    end
end
