#include "incphp.h"

#include <array>
#include <iostream>
#include <cmath>

#include "tclap/CmdLine.h"
#include "carj/carj.h"
#include "carj/ScopedTimer.h"
#include "ipasir/ipasir_cpp.h"

#include "logging.h"
INITIALIZE_EASYLOGGINGPP

int neccessaryArgument = true;
int defaultIsFalse = false;

using json = nlohmann::json;

TCLAP::CmdLine cmd(
	"This tool solves the pidgeon hole principle incrementally.",
	' ', "0.1");

carj::TCarjArg<TCLAP::ValueArg, unsigned> numberOfPigeons("p", "numPigeons",
	"Number of pigeons", !neccessaryArgument, 1, "natural number", cmd);

carj::TCarjArg<TCLAP::ValueArg, unsigned> startingMakeSpan("s", "startingMakeSpan",
	"Makespan to start with.", !neccessaryArgument, 0, "natural number", cmd);

carj::CarjArg<TCLAP::SwitchArg, bool> dimspec("d", "dimspec", "Output dimspec.",
	cmd, defaultIsFalse);


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
	IncrementalFixedPigeons(unsigned _numPigeons):
		numPigeons(_numPigeons),
		numLiteralsPerTime(_numPigeons + 1)
	{

	}

	void solve(){
		auto& solves = carj::getCarj().data["solves"];
		solves.clear();

		bool solved = false;
		for (unsigned makespan = 0; !solved; makespan++) {
			// at most one pigeon in hole of step
			for (unsigned i = 0; i < numPigeons; i++) {
				for (unsigned j = 0; j < i; j++) {
					addClause({
						-varPigeonInHole(i, makespan),
						-varPigeonInHole(j, makespan)});
				}
			}

			if (makespan >= startingMakeSpan.getValue()) {
				// each pigeon has at least one hole
				for (unsigned p = 0; p < numPigeons; p++) {
					std::vector<int> clause;
					for (unsigned h = 0; h <= makespan; h++) {
						clause.push_back(varPigeonInHole(p, h));
					}
					clause.push_back(-activationLiteral(makespan));
					addClause(clause);
				}

				solves.push_back({
					{"makespan", makespan},
					{"time", -1}
				});
				{
					carj::ScopedTimer timer((*solves.rbegin())["time"]);
					solver.assume(activationLiteral(makespan));
					solved = (solver.solve() == ipasir::SolveResult::SAT);
				}
			}
		}
	}

private:
	/**
	 * Variable representing that pigeon p is in hole h.
	 * Note that hole is the same as makespan.
	 */
	int varPigeonInHole(unsigned p, unsigned h) {
		return numLiteralsPerTime * h + p + 2;
	}

	int activationLiteral(unsigned t) {
		return numLiteralsPerTime * t + 1;
	}

	void addClause(std::vector<int> clause) {
		for (int literal: clause) {
			solver.add(literal);
		}
		solver.add(0);
	}

	unsigned numPigeons;
	unsigned numLiteralsPerTime;
	ipasir::Solver solver;
};

int incphp_main(int argc, const char **argv) {
	carj::init(argc, argv, cmd);

	if (dimspec.getValue()) {
		DimSpecFixedPigeons dsfp(numberOfPigeons.getValue());
		dsfp.print();
	} else {
		IncrementalFixedPigeons ifp(numberOfPigeons.getValue());
		ifp.solve();
	}
	return 0;
}
