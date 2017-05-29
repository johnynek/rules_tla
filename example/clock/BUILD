load("//tla:tla.bzl", "tla_module", "tla_simulation", "tlc_test")

tla_module(
    name = "hourclock",
    src = "hourclock.tla")

tlc_test(
    name = "hourclock_sim",
    cfg = "hourclock.cfg",
    module = ":hourclock")
