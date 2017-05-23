package org.bykn.tlc;

import java.io.File;
import java.util.Arrays;
import tlc2.TLC;
import util.SimpleFilenameToStream;

class TlcRunner {

  public static void main(String[] args) {
    try {
      TLC tlc = new TLC();
      // handle parameters
      if (tlc.handleParameters(args)) {
        tlc.setResolver(new SimpleFilenameToStream());
        // call the actual processing method
        tlc.process();
        System.exit(0);
      }
      else {
        System.err.println("Could not handle parameters");
        System.exit(1);
      }

    }
    catch (Throwable t) {
      System.err.println(t.toString());
      System.exit(1);
    }
  }
}
