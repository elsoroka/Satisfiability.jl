@testitem "Extra" begin

    using Logging
    using Satisfiability

    # Extra: Check that defining duplicate variables yields a warning
    @info("Check that redefining a variable yields a warning. One warning will be emitted.")
    @testset "Duplicate variable warning" begin
        SET_DUPLICATE_NAME_WARNING!(true)
        @satvariable(z, Bool)
        @test_logs (:warn, "Duplicate variable name z of type Bool") @satvariable(z, Bool)

        # now we should have no warnings
        SET_DUPLICATE_NAME_WARNING!(false)
        @test_logs min_level = Logging.Warn @satvariable(z, Bool)

        # we can also clear the list
        SET_DUPLICATE_NAME_WARNING!(true)
        CLEAR_VARNAMES!()
        @test_logs min_level = Logging.Warn @satvariable(z, Bool)
        SET_DUPLICATE_NAME_WARNING!(false)
   end
end
