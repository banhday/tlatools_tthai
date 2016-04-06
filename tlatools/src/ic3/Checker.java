package ic3;

import java.io.IOException;
import z3parser.Z3Encoder;

public class Checker {

	public static void main(String[] args) throws IOException {
		// TODO Auto-generated method stub
		for (int i = 0; i < args.length; i++) {
			Z3Encoder z3Encoder = new Z3Encoder(args[i]);
			z3Encoder.run();                    
			IC3_Checker ic3checker = new IC3_Checker(z3Encoder);
			ic3checker.run();
		}
	}

}
