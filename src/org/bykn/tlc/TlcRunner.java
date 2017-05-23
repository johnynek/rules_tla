package org.bykn.tlc;

import java.io.File;
import java.nio.file.Paths;
import java.io.IOException;
import java.rmi.RemoteException;
import java.util.Arrays;
import tlc2.TLC;
import tlc2.TLCGlobals;
import tlc2.tool.ModelChecker;
import tlc2.tool.fp.FPSetConfiguration;
import tlc2.tool.fp.MSBDiskFPSet;
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

  public static void main(String[] args) {
    try {
      File cwd = Paths.get(".").toAbsolutePath().normalize().toFile();

      FPSetConfiguration fpSetConfiguration = new FPSetConfiguration(0.25d,
        SanePathingMultiFPSet.class.getName());
      TLCGlobals.metaDir = System.getProperty("java.io.tmpdir");

      String mainFile = args[0];
      File root = new File(cwd, mainFile).getParentFile();
      int len = mainFile.length();
      if (mainFile.startsWith(".tla", len - 4)) {
        mainFile = mainFile.substring(0, len - 4);
      }

      FilenameToStream resolver0 = new RelativeF2S(root, new SimpleFilenameToStream());
      FilenameToStream resolver = new RelativeF2S(cwd, resolver0);
      ModelChecker mc = new ModelChecker(
          mainFile, // mainFile
          mainFile, // configFile,
          null, // dumpFile,
          false, // asDot,
          false, // deadlock,
          null, // fromChkpt,
          resolver, // resolver,
          null, // specObj,
          fpSetConfiguration);

      // AHhhhhhh GLOBaLS!!!!
      TLCGlobals.mainChecker = mc;
      mc.modelCheck();
      System.exit(0);
    }
    catch (Throwable t) {
      System.err.println(t.toString());
      t.printStackTrace();
      System.exit(1);
    }
  }
}
