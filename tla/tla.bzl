
def _tlc_impl(ctx):
  content = """#!/bin/bash
echo `pwd`
ls -al {input}
{runner} {input}
"""
  content = content.format(
    runner = ctx.executable._tlc.short_path,
    input = ctx.file.input.path)

  ctx.file_action(
    output=ctx.outputs.executable,
    content=content)
  return struct(
      files = set([ctx.outputs.executable]),
      runfiles = ctx.runfiles(
          files = ctx.files._tlc + ctx.files._tla + [ctx.file._java] + ctx.files._jdk + ctx.files.srcs + [ctx.file.input],
          collect_data = True))


tlc_test = rule(
    implementation = _tlc_impl,
    attrs = {
      "srcs": attr.label_list(allow_files = True),
      "input": attr.label(single_file = True, allow_files = True),
      "_tlc": attr.label(default = Label("//src/org/bykn/tlc:tlcrunner"), executable = True, cfg = "host"),
      "_java": attr.label(executable=True, cfg="host", default=Label("@bazel_tools//tools/jdk:java"), single_file=True, allow_files=True),
      "_jdk": attr.label(default=Label("//tools/defaults:jdk"), allow_files=True),
      "_tla": attr.label(default=Label("@tla2tools//jar"), allow_files=True),
    },
    executable = True,
    test = True)
