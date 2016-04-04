package z3parser;

import java.io.*;

public class Wrapper {

	public static void main(String[] args) throws IOException {
		// TODO Auto-generated method stub
		for (int i = 0; i < args.length; i++) {
			Z3Encoder z3Encoder = new Z3Encoder(args[i]);
			z3Encoder.run();					
		//	Z3Worker z3Worker = new Z3Worker(z3Encoder);
		//	z3Worker.run();
		}
	}
}
