
def _tla_module_impl(ctx):
  # todo, run the SANY to check the syntax
  transitive_files = set()
  transitive_files += ctx.files.src
  for dep in ctx.attr.deps:
    transitive_files += dep.default_runfiles.files

  return struct(
      files = set(ctx.files.src),
      tla = struct(module = ctx.files.src[0]),
      runfiles = ctx.runfiles(
          collect_default = True,
          transitive_files = transitive_files,
      )
  )

tla_module = rule(
    implementation = _tla_module_impl,
    attrs = {
        "src": attr.label(allow_files = True),
        "deps": attr.label_list(allow_files = False),
    })

def _runner(ctx, content):
  # set up all the files we need
  transitive_files = set(ctx.attr.module.default_runfiles.files)
  for dep in ctx.attr.deps:
    transitive_files += dep.default_runfiles.files

  ctx.file_action(
    output=ctx.outputs.executable,
    content=content)

  return struct(
      files = set([ctx.outputs.executable]),
      runfiles = ctx.runfiles(
          files = transitive_files.to_list() + ctx.files._tlc + ctx.files._tla + [ctx.file._java] + ctx.files._jdk + [ctx.file.cfg],
          collect_data = True))


def _tlc_impl(ctx):
  # here is the main module:
  mod_src = ctx.attr.module.tla.module

  content = """#!/bin/bash
{runner} check {input} {conf}
"""
  content = content.format(
    runner = ctx.executable._tlc.short_path,
    input = mod_src.short_path,
    conf = ctx.file.cfg.short_path)

  return _runner(ctx, content)

tlc_test = rule(
    implementation = _tlc_impl,
    attrs = {
      "module": attr.label(allow_files = False),
      "cfg": attr.label(single_file = True, allow_files = True),
      "deps": attr.label_list(allow_files = False),
      "_tlc": attr.label(default = Label("//src/org/bykn/tlc:tlcrunner"), executable = True, cfg = "host"),
      "_java": attr.label(executable=True, cfg="host", default=Label("@bazel_tools//tools/jdk:java"), single_file=True, allow_files=True),
      "_jdk": attr.label(default=Label("//tools/defaults:jdk"), allow_files=True),
      "_tla": attr.label(default=Label("@tla2tools//jar"), allow_files=True),
    },
    executable = True,
    test = True)

def _tla_simulation(ctx):
  mod_src = ctx.attr.module.tla.module
  content = """#!/bin/bash
{runner} simulate {input} {conf}
"""
  content = content.format(
    runner = ctx.executable._tlc.short_path,
    input = mod_src.short_path,
    conf = ctx.file.cfg.short_path)

  return _runner(ctx, content)


tla_simulation = rule(
    implementation = _tla_simulation,
    attrs = {
      "module": attr.label(allow_files = False),
      "cfg": attr.label(single_file = True, allow_files = True),
      "deps": attr.label_list(allow_files = False),
      "workers": attr.int(default = 1, values = range(1, 8)),
      "_tlc": attr.label(default = Label("//src/org/bykn/tlc:tlcrunner"), executable = True, cfg = "host"),
      "_java": attr.label(executable=True, cfg="host", default=Label("@bazel_tools//tools/jdk:java"), single_file=True, allow_files=True),
      "_jdk": attr.label(default=Label("//tools/defaults:jdk"), allow_files=True),
      "_tla": attr.label(default=Label("@tla2tools//jar"), allow_files=True),
    },
    executable = True)
