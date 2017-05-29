load("//tla:tla.bzl", "tlc_test", "tla_module")

tla_module(
    name = "TLAPS",
    src = "TLAPS.tla")

tla_module(
    name = "sums_even",
    src = "sums_even.tla",
    deps = [":TLAPS"])

tlc_test(
    name = "sums_even_test",
    module = ":sums_even",
    cfg = "sums_even.cfg")
