#include "incphp.h"

#include "tclap/CmdLine.h"
#include "carj/carj.h"
#include <array>
#include <iostream>
#include <cmath>

int neccessaryArgument = true;
int defaultIsFalse = false;


TCLAP::CmdLine& carj::getCmd() {
	static TCLAP::CmdLine cmdLine(
		"This tool solves the pidgeon hole principle incrementally.",
		' ', "0.1");
	return cmdLine;
}

TCLAP::ValueArg<unsigned> numberOfPigeons("p", "numPigeons",
	"Number of pigeons", !neccessaryArgument, 1, "natural number", carj::getCmd());
TCLAP::SwitchArg dimspec("d", "dimspec", "Output dimspec.",
	carj::getCmd(), defaultIsFalse);


class DimSpecFixedPigeons {
private:
	unsigned numPigeons;
	unsigned numLiteralsPerTime;

	/**
	 * Variable representing that pigeon p is in hole h.
	 * Note that hole is the same as time.
	 */
	int varPigeonInHole(unsigned p, unsigned h) {
		return numLiteralsPerTime * h + p + 1;
	}

	/**
	 * Helper variable, which is true iff the pigeon sits in a future hole.
	 * i.e. step created hole h, then pigeon sits in a hole added in step later
	 */
	int helperFutureHole(int p, int h) {
		return numLiteralsPerTime * h + numPigeons + p + 1;
	}

	void printClause(std::vector<int> clause) {
		for (int literal: clause) {
			std::cout << literal << " ";
		}
		std::cout << "0" << std::endl;
	}

public:
	DimSpecFixedPigeons(unsigned _numPigeons):
		numPigeons(_numPigeons),
		numLiteralsPerTime(2 * _numPigeons)
	{

	}

	void print() {
		//i, u, g, t
		int numberOfClauses = 0;
		numberOfClauses = numPigeons;
		std::cout << "i cnf " << numLiteralsPerTime << " "
			<< numberOfClauses << std::endl;
		for (unsigned i = 0; i < numPigeons; i++) {
			printClause({
				varPigeonInHole(i, 0), helperFutureHole(i, 0)
			});
		}

		numberOfClauses = (numPigeons - 1) * numPigeons / 2;
		std::cout << "u cnf " << numLiteralsPerTime << " "
			<< numberOfClauses << std::endl;
		// at most one pigeon in hole of step
		for (unsigned i = 0; i < numPigeons; i++) {
			for (unsigned j = 0; j < i; j++) {
				printClause({-varPigeonInHole(i, 0) , -varPigeonInHole(j, 0)});
			}
		}

		numberOfClauses = numPigeons;
		std::cout << "g cnf " << numLiteralsPerTime << " "
			<< numberOfClauses << std::endl;
		for (unsigned i = 0; i < numPigeons; i++) {
			printClause({-helperFutureHole(i, 0)});
		}

		numberOfClauses = 3 * numPigeons;
		std::cout << "t cnf " << 2 * numLiteralsPerTime << " "
			<< numberOfClauses << std::endl;
		for (unsigned i = 0; i < numPigeons; i++) {
			// ->
			printClause({
				-helperFutureHole(i, 0),
				varPigeonInHole(i, 1),
				helperFutureHole(i, 1),
			});

			// <-
			printClause({
				helperFutureHole(i, 0),
				-varPigeonInHole(i, 1)
			});
			printClause({
				helperFutureHole(i, 0),
				-helperFutureHole(i, 1)
			});
		}
	}
};

class IncrementalFixedPigeons {
public:
	IncrementalFixedPigeons(unsigned _numPigeons)
	{

	}
};

int incphp_main(int argc, const char **argv) {
	carj::init(argc, argv);

	if (dimspec.getValue()) {
		DimSpecFixedPigeons dsfp(numberOfPigeons.getValue());
		dsfp.print();
	}
	return 0;
}
