// host_main.cpp - the program's interface for the evaluation service. NOT part of the solver: this file must stay
// byte-identical (the build refuses a tree in which it differs).
//
//   prog <instance file> <time limit in seconds> <seed> <solution file>
//
// One run. Instance file: first line n, then one line "v: neighbours" per vertex 0..n-1, then a LAST line "K <k>" =
// the number of vertices to remove (the solver's reader stops after the n vertex lines). The best solution found is
// written to the solution file: line 1 the k removed vertices, line 2 the objective value the solver reports (the
// service recomputes it). One line with the result goes to the standard output.
//
// Seeding: the solver calls srand(cnp_clock()) where the published program called srand(time(NULL)).
// cnp_clock() = seed * 100003 + the whole seconds since the program started: the same clock, started at a point that
// the seed decides instead of at the calendar time.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static unsigned RunSeed = 1;
static time_t WallStart;
unsigned cnp_clock() { return RunSeed * 100003u + (unsigned)(time(NULL) - WallStart); }

#include "solver.cpp"

static int last_line_K(const char *path)
{
	FILE *f = fopen(path, "rb");
	if(f == NULL) return -1;
	char line[256], last[256];
	last[0] = 0;
	while(fgets(line, sizeof(line), f) != NULL)
	{
		const char *q = line;
		while(*q == ' ' || *q == '\t' || *q == '\r' || *q == '\n') q++;
		if(*q != 0) strcpy(last, q);
	}
	fclose(f);
	int k = -1;
	if(sscanf(last, "K %d", &k) != 1) return -1;
	return k;
}

int main(int argc, char **argv)
{
	if(argc != 5)
	{
		fprintf(stderr, "usage: prog <instance file> <time limit in seconds> <seed> <solution file>\n");
		return 2;
	}
	static char name[] = "instance";
	InstanceName = name;
	LimitTime = atof(argv[2]);
	RunSeed = (unsigned)strtoul(argv[3], NULL, 10);
	BKV = -1;		// no best-known value: the search uses the whole time limit
	OF = false;
	K = last_line_K(argv[1]);
	WallStart = time(NULL);
	read_instance(argv[1]);
	if(K < 1 || K >= NbrV)
	{
		fprintf(stderr, "bad K (%d) for n = %d\n", K, NbrV);
		return 2;
	}
	srand(cnp_clock());
	setup_data();
	Instance_Reduction_Based_Search_CNP();
	check_result(BestRemovedV, NbrBestRemovedV, BestObjValue, BestNbrC);
	FILE *out = fopen(argv[4], "w");
	if(out == NULL)
	{
		fprintf(stderr, "cannot write %s\n", argv[4]);
		return 3;
	}
	for(int i = 0; i < NbrBestRemovedV; i++)
		fprintf(out, "%d ", BestRemovedV[i]);
	fprintf(out, "\n%d\n", BestObjValue);
	fclose(out);
	printf("RESULT n %d k %d objective %d best_time %.3f generations %lu\n", NbrV, K, BestObjValue, BestTime, BestNbrGens);
	return 0;
}
