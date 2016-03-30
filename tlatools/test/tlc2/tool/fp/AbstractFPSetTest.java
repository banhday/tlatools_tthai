// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp;

import java.io.File;
import java.io.IOException;
import java.text.DecimalFormat;
import java.util.Date;
import org.junit.After;
import org.junit.Before;

public abstract class AbstractFPSetTest {

	protected static final long RNG_SEED = 15041980L;

	protected static final String tmpdir = System.getProperty("java.io.tmpdir") + File.separator + "FPSetTest"
					+ System.currentTimeMillis();
	protected static final String filename = "FPSetTestTest";
	protected static final DecimalFormat df = new DecimalFormat("###,###.###");

	protected long previousTimestamp;
	protected long previousSize;
	protected Date endTimeStamp;

	private File dir;
	

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#setUp()
	 */
	@Before
	public void setUp() throws Exception {
		// create temp folder
		dir = new File(tmpdir);
		dir.mkdirs();
		
		previousTimestamp = System.currentTimeMillis();
		previousSize = 0L;
		
		System.out.println("Test started at " + new Date());
	}

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#tearDown()
	 */
	@After
	public void tearDown() {
		if (endTimeStamp == null) {
			endTimeStamp = new Date();
		}
		System.out.println("Test finished at " + endTimeStamp);
		
		// delete all nested files
		final File[] listFiles = dir.listFiles();
		for (int i = 0; i < listFiles.length; i++) {
			final File aFile = listFiles[i];
			aFile.delete();
		}
		dir.delete();
	}

	/**
	 * @param freeMemory
	 * @return A new {@link FPSet} instance
	 * @throws IOException
	 */
	protected abstract FPSet getFPSet(final FPSetConfiguration fpSetConfig) throws IOException;

	protected FPSet getFPSetInitialized() throws IOException {
		return getFPSetInitialized(1);
	}
	
	protected FPSet getFPSetInitialized(int numThreads) throws IOException {
		final FPSet fpSet = getFPSet(new FPSetConfiguration());
		fpSet.init(numThreads, tmpdir, filename);

		if (fpSet instanceof FPSetStatistic) {
			FPSetStatistic fpSetStats = (FPSetStatistic) fpSet;
			long maxTblCnt = fpSetStats.getMaxTblCnt();
			System.out.println("Maximum FPSet bucket count is: "
					+ df.format(maxTblCnt) + " (approx: "
					+ df.format(maxTblCnt * FPSet.LongSize >> 20) + " GiB)");
		}

		System.out.println("Testing " + fpSet.getClass().getCanonicalName());
		return fpSet;
	}

	// insertion speed
	public void printInsertionSpeed(final long currentSize) {
		final long currentTimestamp = System.currentTimeMillis();
		// print every minute
		final double factor = (currentTimestamp - previousTimestamp) / 60000d;
		if (factor >= 1d) {
			long insertions = (long) ((currentSize - previousSize) * factor);
			System.out.println(df.format(insertions) + " insertions/min");
			previousTimestamp = currentTimestamp;
			previousSize = currentSize;
		}
	}
}
