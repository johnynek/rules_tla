package org.bykn.tlc;

import java.io.File;
import java.io.IOException;
import java.nio.file.Paths;
import java.rmi.RemoteException;
import java.util.Arrays;
import tlc2.TLC;
import tlc2.TLCGlobals;
import tlc2.tool.ModelChecker;
import tlc2.tool.Simulator;
import tlc2.tool.fp.FPSetConfiguration;
import tlc2.tool.fp.MSBDiskFPSet;
import tlc2.util.FP64;
import tlc2.util.RandomGenerator;
import util.FileUtil;
import util.FilenameToStream;
import util.SimpleFilenameToStream;

class TlcRunner {

  /**
   * The TLA code assumes that paths are in the current directory.
   * I am trying to hack around that but it is a little painful...
   */
  static public class SanePathingMultiFPSet extends MSBDiskFPSet {
    public SanePathingMultiFPSet(final FPSetConfiguration fpSetConfiguration) throws RemoteException {
      super(fpSetConfiguration);
    }
    @Override
    public void init(int numThreads, String aMetadir, String filename) throws IOException {
      // This is the file it expects, but it assumes filename has no /
      String path = aMetadir + FileUtil.separator + filename + ".tmp";
      File parent = new File(path).getParentFile();
      parent.mkdirs();
      super.init(numThreads, aMetadir, filename);
    }
  }

  /**
   * This is also to deal with paths that are not in the current directory...
   */
  static class RelativeF2S implements FilenameToStream {
    private final File _root;
    private final FilenameToStream _fallback;

    public RelativeF2S(File root, FilenameToStream fallback) {
      _root = root;
      _fallback = fallback;
    }

    @Override
    public File resolve(String filename, boolean isModule) {
      //System.out.println(filename);
      //System.out.println(_root);
      File test0 = new File(_root, filename);
      File test1 = new File(filename);
      if (test0.exists()) {
        return test0;
      }
      else if (test1.exists()) {
        return test1;
      }
      else {
        return _fallback.resolve(filename, isModule);
      }
    }

    @Override
    public String getFullPath() {
      String path = _fallback.getFullPath();
      String rstr = _root.toString();
      if (path.equals("")) {
        return rstr;
      }
      else {
        return path + ", " + rstr;
      }
    }

    @Override
    public boolean isStandardModule(String moduleName) {
      return _fallback.isStandardModule(moduleName);
    }
  }

  private static FilenameToStream getResolver(File cwd, String mainFile) {
    File root = new File(cwd, mainFile).getParentFile();
    FilenameToStream resolver0 = new RelativeF2S(root, new SimpleFilenameToStream());
    FilenameToStream resolver = new RelativeF2S(cwd, resolver0);

    return resolver;
  }

  private static void modelCheck(File cwd, String mainFile, String conf) throws Throwable {
    FPSetConfiguration fpSetConfiguration = new FPSetConfiguration(0.25d,
      SanePathingMultiFPSet.class.getName());
    TLCGlobals.metaDir = System.getProperty("java.io.tmpdir");

    FilenameToStream resolver = getResolver(cwd, mainFile);

    int len = mainFile.length();
    if (mainFile.startsWith(".tla", len - 4)) {
      mainFile = mainFile.substring(0, len - 4);
    }
    len = conf.length();
    if (conf.startsWith(".cfg", len - 4)) {
      conf = conf.substring(0, len - 4);
    }

    ModelChecker mc = new ModelChecker(
        mainFile, // mainFile
        conf, // configFile,
        null, // dumpFile,
        false, // asDot,
        false, // deadlock,
        null, // fromChkpt,
        resolver, // resolver,
        null, // specObj,
        fpSetConfiguration);

    // AHhhhhhh GLOBaLS!!!!
    TLCGlobals.mainChecker = mc;
    mc.doInit(false);
    mc.modelCheck();
  }

  private static void simulate(File cwd, String mainFile, String conf) throws Exception {
    FPSetConfiguration fpSetConfiguration = new FPSetConfiguration(0.25d,
      SanePathingMultiFPSet.class.getName());
    TLCGlobals.metaDir = System.getProperty("java.io.tmpdir");

    FilenameToStream resolver = getResolver(cwd, mainFile);

    int len = mainFile.length();
    if (mainFile.startsWith(".tla", len - 4)) {
      mainFile = mainFile.substring(0, len - 4);
    }
    len = conf.length();
    if (conf.startsWith(".cfg", len - 4)) {
      conf = conf.substring(0, len - 4);
    }
    // random simulation
    RandomGenerator rng = new RandomGenerator();
    long seed = rng.nextLong();
    rng.setSeed(seed);
    Simulator simulator =
      new Simulator(
          mainFile,
          conf,
          null,
          true, // check for deadlocks
          80, // traceDepth
          1 << 20, // traceNum
          rng,
          seed,
          true,
          resolver,
          null // specObj
          );

    TLCGlobals.simulator = simulator;
    simulator.simulate();
  }

  public static void main(String[] args) {
    try {
      File cwd = Paths.get(".").toAbsolutePath().normalize().toFile();
      String mode = args[0];
      String mainFile = args[1];
      String conf = args[2];
      FP64.Init(0);
      //use some constant (fpIndex < 0 || fpIndex >= FP64.Polys.length)
      if (mode.equals("check")) {
        modelCheck(cwd, mainFile, conf);
      }
      else if (mode.equals("simulate")) {
        simulate(cwd, mainFile, conf);
      }
      else {
        throw new Exception("unknown mode: " + mode);
      }
      System.exit(0);
    }
    catch (Throwable t) {
      System.err.println(t.toString());
      t.printStackTrace();
      System.exit(1);
    }
  }
}
