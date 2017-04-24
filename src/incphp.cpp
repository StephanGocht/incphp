#include "incphp.h"

#include <array>
#include <iostream>
#include <cmath>

#include "SatVariable.h"

#include "tclap/CmdLine.h"
#include "carj/carj.h"
#include "carj/ScopedTimer.h"
#include "ipasir/ipasir_cpp.h"
#include "ipasir/printer.h"

#include "carj/logging.h"

int neccessaryArgument = true;
int defaultIsFalse = false;

using json = nlohmann::json;

TCLAP::CmdLine cmd(
	"This tool solves the pidgeon hole principle incrementally.",
	' ', "0.1");

carj::TCarjArg<TCLAP::ValueArg, unsigned> startingMakeSpan("s", "startingMakeSpan",
	"Makespan to start with.", !neccessaryArgument, 0, "natural number", cmd);


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
			// printClause({
			// 	helperFutureHole(i, 0),
			// 	-varPigeonInHole(i, 1)
			// });
			// printClause({
			// 	helperFutureHole(i, 0),
			// 	-helperFutureHole(i, 1)
			// });
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
		auto& solves = carj::getCarj()
			.data["/incphp/result/solves"_json_pointer];
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

class ExtendedResolution {
public:
	ExtendedResolution(unsigned _numPigeons):
		numPigeons(_numPigeons)
	{

	}

	void solve(){
		unsigned sn = numPigeons;

		// at most one pigeon in hole h
		for (unsigned h = 0; h < numPigeons - 1; h++) {
			for (unsigned i = 0; i < numPigeons; i++) {
				for (unsigned j = 0; j < i; j++) {
					addClause({
						-P(sn, i, h),
						-P(sn, j, h)});
				}
			}
		}

		// each pigeon has at least one hole
		for (unsigned p = 0; p < numPigeons; p++) {
			std::vector<int> clause;
			for (unsigned h = 0; h < numPigeons - 1; h++) {
				clause.push_back(P(sn, p, h));
			}
			addClause(clause);
		}

		for (unsigned n = sn; n > 2; n--) {
			for (unsigned i = 0; i < n - 1; i++) {
				for (unsigned j = 0; j < n - 2; j++) {
					addClause({
						 P(n - 1, i, j),
						-P(n, i, j)
					});
					addClause({
						 P(n - 1, i, j),
						-P(n, i, n - 2),
						-P(n, n - 1, j)
					});
					addClause({
						-P(n - 1, i, j),
						 P(n, i, j),
						 P(n, i, n - 2)
					});
					addClause({
						-P(n - 1, i, j),
						 P(n, i, j),
						 P(n, n - 1, j)
					});
				}
			}
		}

		auto& solves = carj::getCarj()
			.data["/incphp/result/solves"_json_pointer];
		solves.clear();
		LOG(INFO) << "At most one";
		for (unsigned makespan = 0; makespan < numPigeons; makespan++) {
			solves.push_back({
				{"makespan", makespan},
				{"time", -1}
			});
			LOG(INFO) << "Makespan: " << makespan;
			carj::ScopedTimer timer((*solves.rbegin())["time"]);

			for (unsigned h = 0; h < numPigeons - 1 - makespan; h++) {
				for (unsigned p = 1; p < numPigeons - makespan; p++) {
					for (unsigned j = 0; j < p; j++) {
					//carj::ScopedTimer timer((*solves.rbegin())["time"]);
					//LOG(INFO) << "P(" << sn - makespan << ", " << p << ", " << h << ")";
					//LOG(INFO) << "P(" << sn - makespan << ", " << j << ", " << h << ")";
					solver.assume(P(sn - makespan, p, h));
					solver.assume(P(sn - makespan, j, h));
					bool solved = (solver.solve() == ipasir::SolveResult::SAT);
					assert(!solved);
					}
				}
			}

			for (unsigned p = 1; p < numPigeons - makespan; p++) {
				for (unsigned h = 0; h < numPigeons - 1 - makespan; h++) {
					//carj::ScopedTimer timer((*solves.rbegin())["time"]);
					//LOG(INFO) << "P(" << sn - makespan << ", " << p << ", " << h << ")";
					//LOG(INFO) << "P(" << sn - makespan << ", " << j << ", " << h << ")";
					solver.assume(-P(sn - makespan, p, h));
				}
				bool solved = (solver.solve() == ipasir::SolveResult::SAT);
				assert(!solved);
			}
		}

		// LOG(INFO) << "At Least one";
		// for (unsigned makespan = 0; makespan < numPigeons; makespan++) {
		// 	solves.push_back({
		// 		{"makespan", makespan},
		// 		{"time", -1}
		// 	});
		// 	LOG(INFO) << "Makespan: " << makespan;
		// 	carj::ScopedTimer timer((*solves.rbegin())["time"]);

		// 	for (unsigned p = 1; p < numPigeons - makespan; p++) {
		// 		for (unsigned h = 0; h < numPigeons - 1 - makespan; h++) {
		// 			//carj::ScopedTimer timer((*solves.rbegin())["time"]);
		// 			//LOG(INFO) << "P(" << sn - makespan << ", " << p << ", " << h << ")";
		// 			//LOG(INFO) << "P(" << sn - makespan << ", " << j << ", " << h << ")";
		// 			solver.assume(-P(sn - makespan, p, h));
		// 		}
		// 		bool solved = (solver.solve() == ipasir::SolveResult::SAT);
		// 		assert(!solved);
		// 	}
		// }

		LOG(INFO) << "Final solve";
		bool solved = (solver.solve() == ipasir::SolveResult::SAT);
		assert(!solved);
		solved = (solver.solve() == ipasir::SolveResult::SAT);
		assert(!solved);
	}

private:
	ipasir::Solver solver;
	unsigned numPigeons;

	/**
	 * Variable representing that pigeon p is in hole h.
	 */
	int P(unsigned n, unsigned p, unsigned h) {
		return ((n * numPigeons + p) * numPigeons + h) + 1;
	}


	void addClause(std::vector<int> clause) {
		for (int literal: clause) {
			solver.add(literal);
		}
		solver.add(0);
	}
};

class ExtendedResolution3 {
public:
	ExtendedResolution3(unsigned _numPigeons):
		numPigeons(_numPigeons),
		allocator(),
		H(allocator.newVariable(numPigeons, numPigeons)),
		P(allocator.newVariable(numPigeons + 1, numPigeons, numPigeons))
	{

	}

	void solve(){
		unsigned sn = numPigeons;

		// at most one pigeon in hole h
		for (unsigned h = 0; h < numPigeons - 1; h++) {
			for (unsigned i = 0; i < numPigeons; i++) {
				for (unsigned j = 0; j < i; j++) {
					addClause({
						-P(sn, i, h),
						-P(sn, j, h)});
				}
			}
		}

		// each pigeon has at least one hole
		for (unsigned p = 0; p < numPigeons; p++) {
			for (unsigned h = 0; h < numPigeons - 1; h++) {
				addClause({
					-H(p,h),
					P(sn, p, h),
					H(p, h + 1)
				});
			}
			addClause({H(p,0)});
			addClause({-H(p,numPigeons - 1)});
		}

		for (unsigned n = sn; n > 2; n--) {
			for (unsigned i = 0; i < n - 1; i++) {
				for (unsigned j = 0; j < n - 2; j++) {
					addClause({
						 P(n - 1, i, j),
						-P(n, i, j)
					});
					addClause({
						 P(n - 1, i, j),
						-P(n, i, n - 2),
						-P(n, n - 1, j)
					});
					addClause({
						-P(n - 1, i, j),
						 P(n, i, j),
						 P(n, i, n - 2)
					});
					addClause({
						-P(n - 1, i, j),
						 P(n, i, j),
						 P(n, n - 1, j)
					});
				}
			}
		}

		auto& solves = carj::getCarj()
			.data["/incphp/result/solves"_json_pointer];
		solves.clear();
		LOG(INFO) << "At most one";
		for (unsigned makespan = 0; makespan < numPigeons; makespan++) {
			solves.push_back({
				{"makespan", makespan},
				{"time", -1}
			});
			LOG(INFO) << "Makespan: " << makespan;
			carj::ScopedTimer timer((*solves.rbegin())["time"]);

			// learn at most one
			for (unsigned h = 0; h < numPigeons - 1 - makespan; h++) {
				for (unsigned p = 1; p < numPigeons - makespan; p++) {
					for (unsigned j = 0; j < p; j++) {
					//carj::ScopedTimer timer((*solves.rbegin())["time"]);
					//LOG(INFO) << "P(" << sn - makespan << ", " << p << ", " << h << ")";
					//LOG(INFO) << "P(" << sn - makespan << ", " << j << ", " << h << ")";
					solver.assume(P(sn - makespan, p, h));
					solver.assume(P(sn - makespan, j, h));
					bool solved = (solver.solve() == ipasir::SolveResult::SAT);
					assert(!solved);
					}
				}
			}

			// // learn at least one
			// for (unsigned p = 1; p < numPigeons - makespan; p++) {
			// 	for (unsigned h = 0; h < numPigeons - 1 - makespan; h++) {
			// 		//carj::ScopedTimer timer((*solves.rbegin())["time"]);
			// 		//LOG(INFO) << "P(" << sn - makespan << ", " << p << ", " << h << ")";
			// 		//LOG(INFO) << "P(" << sn - makespan << ", " << j << ", " << h << ")";
			// 		solver.assume(-P(sn - makespan, p, h));
			// 	}
			// 	bool solved = (solver.solve() == ipasir::SolveResult::SAT);
			// 	assert(!solved);
			// }
		}

		LOG(INFO) << "Final solve";
		bool solved = (solver.solve() == ipasir::SolveResult::SAT);
		assert(!solved);
		solved = (solver.solve() == ipasir::SolveResult::SAT);
		assert(!solved);
	}

private:
	ipasir::Solver solver;
	unsigned numPigeons;

	SatVariableAllocator allocator;
	SatVariable<unsigned, unsigned> H;
	SatVariable<unsigned, unsigned, unsigned> P;

	void addClause(std::vector<int> clause) {
		for (int literal: clause) {
			solver.add(literal);
		}
		solver.add(0);
	}
};

class VariableContainer {
public:
	VariableContainer(unsigned _numPigeons):
		numPigeons(_numPigeons),
		allocator()
	{

	}

	virtual int pigeonInHole(unsigned pigeon, unsigned hole) = 0;

	virtual SatVariableAllocator& getAllocator() {
		return allocator;
	}

	virtual ~VariableContainer(){

	}
protected:
	unsigned numPigeons;

private:
	SatVariableAllocator allocator;
};

class BasicVariableContainer: public virtual VariableContainer {
public:
	BasicVariableContainer(unsigned numPigeons):
		VariableContainer(numPigeons),
		P(VariableContainer::getAllocator().newVariable(
			numPigeons, numPigeons - 1)) {

	}

	virtual int pigeonInHole(unsigned pigeon, unsigned hole) {
		return P(pigeon, hole);
	}

	virtual ~BasicVariableContainer(){

	}

private:
	SatVariable<unsigned, unsigned> P;
};

class ExtendedVariableContainer: public virtual VariableContainer {
public:
	ExtendedVariableContainer(unsigned numPigeons):
		VariableContainer(numPigeons),
		P(VariableContainer::getAllocator().newVariable(
			numPigeons + 1, numPigeons, numPigeons - 1)) {

	}
	virtual int pigeonInHole(unsigned pigeon, unsigned hole) {
		return P(numPigeons, pigeon, hole);
	}

	virtual int pigeonInHole(unsigned layer, unsigned pigeon, unsigned hole) {
		return P(layer, pigeon, hole);
	}

	virtual ~ExtendedVariableContainer(){

	}
private:
	SatVariable<unsigned, unsigned, unsigned> P;
};

class VariableContainer3SAT: public virtual VariableContainer {
public:
	VariableContainer3SAT(unsigned numPigeons):
		VariableContainer(numPigeons),
		H(getAllocator().newVariable(numPigeons, numPigeons))
	{
	}

	virtual int connector(unsigned pigeon, unsigned hole) {
		return H(pigeon, hole);
	}

	virtual ~VariableContainer3SAT(){

	}
private:
	SatVariable<unsigned, unsigned> H;
};

class HelperVariableContainer: public virtual VariableContainer {
public:
	HelperVariableContainer(unsigned numPigeons):
		VariableContainer(numPigeons),
		helperVar(getAllocator().newVariable(numPigeons))
	{
	}

	virtual int helper(unsigned i) {
		return helperVar(i);
	}

	virtual ~HelperVariableContainer(){

	}

private:
	SatVariable<unsigned> helperVar;
};

template <class T1, class T2>
class ContainerCombinator:
		public virtual VariableContainer,
		public virtual T1,
		public virtual T2 {

public:
	ContainerCombinator(unsigned numPigeons):
		VariableContainer(numPigeons),
		T1(numPigeons),
		T2(numPigeons)
	{
	}

	virtual ~ContainerCombinator(){

	}
};

class UniversalPHPEncoder {
public:
	UniversalPHPEncoder(
		std::unique_ptr<ipasir::Ipasir> _solver,
		unsigned _numPigeons):

		UniversalPHPEncoder(
			std::move(_solver),
			std::make_unique<BasicVariableContainer>(_numPigeons),
			_numPigeons
		)
	{}

	UniversalPHPEncoder(
		std::unique_ptr<ipasir::Ipasir> _solver,
		std::unique_ptr<VariableContainer> _var,
		unsigned _numPigeons):
			solver(std::move(_solver)),
			var(std::move(_var)),
			numPigeons(_numPigeons)
	{
		assert(numPigeons > 1);
	}

	virtual void addAtMostOnePigeonInHole(unsigned hole) {
		for (unsigned pigeonA = 1; pigeonA < numPigeons; pigeonA++) {
			for (unsigned pigeonB = 0; pigeonB < pigeonA; pigeonB++) {
				solver->addClause({
					-var->pigeonInHole(pigeonA, hole),
					-var->pigeonInHole(pigeonB, hole)
				});
			}
		}
	}

	virtual void addAtLeastOneHolePerPigeon(
			unsigned numHoles,
			unsigned activationLiteral = 0) {

		for (unsigned pigeon = 0; pigeon < numPigeons; pigeon++) {
			for (unsigned hole = 0; hole < numHoles; hole++) {
				solver->add(var->pigeonInHole(pigeon, hole));
			}
			if (activationLiteral != 0) {
				solver->add(activationLiteral);
			}
			solver->add(0);
		}
	}

	virtual void solve(){
		unsigned numHoles = numPigeons - 1;

		addAtLeastOneHolePerPigeon(numHoles);
		for (unsigned hole = 0; hole < numHoles; hole++) {
			addAtMostOnePigeonInHole(hole);
		}
		bool solved = (solver->solve() == ipasir::SolveResult::SAT);
		assert(!solved);
	}

	virtual VariableContainer* getVar() {
		return var.get();
	}

	virtual ~UniversalPHPEncoder(){

	}

protected:
	std::unique_ptr<ipasir::Ipasir> solver;
	std::unique_ptr<VariableContainer> var;
	unsigned numPigeons;
};

typedef ContainerCombinator<HelperVariableContainer, BasicVariableContainer> hvc;

class SimpleIncrementalPHPEncoder: public UniversalPHPEncoder {
public:
	SimpleIncrementalPHPEncoder(
		std::unique_ptr<ipasir::Ipasir> _solver,
		unsigned numPigeons):

		UniversalPHPEncoder(
				std::move(_solver),
				std::make_unique<hvc>(numPigeons),
				numPigeons
			)
		{
			hvar = dynamic_cast<hvc*>(getVar());
		}

	virtual void solve(){
		bool solved;
		for (unsigned numHoles = 1; numHoles < numPigeons; numHoles++) {
			addAtMostOnePigeonInHole(numHoles - 1);
			addAtLeastOneHolePerPigeon(numHoles, hvar->helper(numHoles - 1));

			solver->assume(-hvar->helper(numHoles - 1));
			solved = (solver->solve() == ipasir::SolveResult::SAT);
			assert(!solved);
		}
	}

	virtual ~SimpleIncrementalPHPEncoder(){}

private:
	hvc* hvar;
};

typedef ContainerCombinator<VariableContainer3SAT, BasicVariableContainer> svc;

class PHPEncoder3SAT: public UniversalPHPEncoder {
public:
	PHPEncoder3SAT(
		std::unique_ptr<ipasir::Ipasir> _solver,
		unsigned _numPigeons):
		UniversalPHPEncoder(
			std::move(_solver),
			std::make_unique<svc>(_numPigeons),
			_numPigeons
		) {

	}

	PHPEncoder3SAT(
			std::unique_ptr<ipasir::Ipasir> _solver,
			std::unique_ptr<VariableContainer3SAT> _var,
			unsigned _numPigeons):

			UniversalPHPEncoder(
				std::move(_solver),
				std::move(_var),
				_numPigeons
				)
		{

		}

	virtual void addBorders() {
		VariableContainer3SAT* var =
			dynamic_cast<VariableContainer3SAT*>(getVar());

		for (unsigned p = 0; p < numPigeons; p++) {
			solver->addClause({ var->connector(p, 0)});
			solver->addClause({-var->connector(p, numPigeons - 1)});
		}
	}

	virtual void addHole(unsigned hole) {
		VariableContainer3SAT* var =
			dynamic_cast<VariableContainer3SAT*>(getVar());

		for (unsigned p = 0; p < numPigeons; p++) {
			solver->addClause({
				-var->connector(p,hole),
				 var->pigeonInHole(p, hole),
				 var->connector(p, hole + 1)
			});
		}

		addAtMostOnePigeonInHole(hole);
	}

	virtual void assumeAll(unsigned i) {
		VariableContainer3SAT* var =
			dynamic_cast<VariableContainer3SAT*>(getVar());

		for (unsigned p = 0; p < numPigeons; p++) {
			solver->assume(-var->connector(p, i));
		}
	}

	virtual void solve() {
		solve(false);
	}

	virtual void solveIncremental() {
		solve(true);
	}

	virtual void solve(bool incremental){
		bool solved;
		addBorders();
		for (unsigned numHoles = 1; numHoles < numPigeons; numHoles++) {
			addHole(numHoles - 1);

			if (incremental) {
				assumeAll(numHoles);
				solved = (solver->solve() == ipasir::SolveResult::SAT);
				assert(!solved);
			}
		}

		if (!incremental) {
			solved = (solver->solve() == ipasir::SolveResult::SAT);
			assert(!solved);
		}
	}

	virtual ~PHPEncoder3SAT() {};
};

typedef ContainerCombinator<ExtendedVariableContainer, VariableContainer3SAT> evc;

class ExtendedPHPEncoder3SAT: public PHPEncoder3SAT {
public:
	ExtendedPHPEncoder3SAT(
		std::unique_ptr<ipasir::Ipasir> _solver,
		unsigned _numPigeons):

		PHPEncoder3SAT(
			std::move(_solver),
			std::make_unique<evc>(_numPigeons),
			_numPigeons
		)
	{
	}

	ExtendedPHPEncoder3SAT(
		std::unique_ptr<ipasir::Ipasir> _solver,
		std::unique_ptr<evc> _var,
		unsigned _numPigeons):

		PHPEncoder3SAT(
			std::move(_solver),
			std::move(_var),
			_numPigeons
			)
	{
	}

	virtual void addExtendedResolutionClauses(){
		ExtendedVariableContainer* var =
			dynamic_cast<ExtendedVariableContainer*>(getVar());

		for (unsigned n = numPigeons; n > 2; n--) {
			for (unsigned i = 0; i < n - 1; i++) {
				for (unsigned j = 0; j < n - 2; j++) {
					solver->addClause({
						 var->pigeonInHole(n - 1, i, j),
						-var->pigeonInHole(n, i, j)
					});
					solver->addClause({
						 var->pigeonInHole(n - 1, i, j),
						-var->pigeonInHole(n, i, n - 2),
						-var->pigeonInHole(n, n - 1, j)
					});
					solver->addClause({
						-var->pigeonInHole(n - 1, i, j),
						 var->pigeonInHole(n, i, j),
						 var->pigeonInHole(n, i, n - 2)
					});
					solver->addClause({
						-var->pigeonInHole(n - 1, i, j),
						 var->pigeonInHole(n, i, j),
						 var->pigeonInHole(n, n - 1, j)
					});
				}
			}
		}
	}

	virtual void learnClauses(unsigned step){
		unsigned sn = numPigeons;
		ExtendedVariableContainer* var =
			dynamic_cast<ExtendedVariableContainer*>(getVar());


			// learn at most one
			for (unsigned h = 0; h < numPigeons - 1 - step; h++) {
				for (unsigned p = 1; p < numPigeons - step; p++) {
					for (unsigned j = 0; j < p; j++) {
					//carj::ScopedTimer timer((*solves.rbegin())["time"]);
					//LOG(INFO) << "var->pigeonInHole(" << sn - step << ", " << p << ", " << h << ")";
					//LOG(INFO) << "var->pigeonInHole(" << sn - step << ", " << j << ", " << h << ")";
					solver->assume(var->pigeonInHole(sn - step, p, h));
					solver->assume(var->pigeonInHole(sn - step, j, h));
					bool solved = (solver->solve() == ipasir::SolveResult::SAT);
					assert(!solved);
					}
				}
			}

			// learn at least one
			for (unsigned p = 1; p < numPigeons - step; p++) {
				for (unsigned h = 0; h < numPigeons - 1 - step; h++) {
					//carj::ScopedTimer timer((*solves.rbegin())["time"]);
					//LOG(INFO) << "var->pigeonInHole(" << sn - step << ", " << p << ", " << h << ")";
					//LOG(INFO) << "var->pigeonInHole(" << sn - step << ", " << j << ", " << h << ")";
					solver->assume(-var->pigeonInHole(sn - step, p, h));
				}
				bool solved = (solver->solve() == ipasir::SolveResult::SAT);
				assert(!solved);
			}
	}

	virtual void solve() {
		solve(false);
	}

	virtual void solveIncremental() {
		solve(true);
	}

	virtual void solve(bool incremental){
		bool solved;
		addBorders();
		for (unsigned numHoles = 1; numHoles < numPigeons; numHoles++) {
			addHole(numHoles - 1);
		}
		addExtendedResolutionClauses();

		if (incremental) {
			for (unsigned step = 0; step < numPigeons; step++) {
				learnClauses(step);
			}
		}

		solved = (solver->solve() == ipasir::SolveResult::SAT);
		assert(!solved);
	}

	virtual ~ExtendedPHPEncoder3SAT(){

	}
};


class IncrementalExtendedResolution3 {
public:
	IncrementalExtendedResolution3(unsigned _numPigeons):
		numPigeons(_numPigeons),
		allocator(),
		H(allocator.newVariable(numPigeons, numPigeons)),
		P(allocator.newVariable(numPigeons + 1, numPigeons, numPigeons))
	{

	}

	void solve(){
		unsigned sn = numPigeons;

		// at most one pigeon in hole h
		for (unsigned h = 0; h < numPigeons - 1; h++) {
			for (unsigned i = 0; i < numPigeons; i++) {
				for (unsigned j = 0; j < i; j++) {
					addClause({
						-P(sn, i, h),
						-P(sn, j, h)});
				}
			}
		}

		for (unsigned n = sn; n > 2; n--) {
			for (unsigned i = 0; i < n - 1; i++) {
				for (unsigned j = 0; j < n - 2; j++) {
					addClause({
						 P(n - 1, i, j),
						-P(n, i, j)
					});
					addClause({
						 P(n - 1, i, j),
						-P(n, i, n - 2),
						-P(n, n - 1, j)
					});
					addClause({
						-P(n - 1, i, j),
						 P(n, i, j),
						 P(n, i, n - 2)
					});
					addClause({
						-P(n - 1, i, j),
						 P(n, i, j),
						 P(n, n - 1, j)
					});
				}
			}
		}

		for (unsigned makespan = 0; makespan < numPigeons; makespan++) {
			// learn at most one
			for (unsigned h = 0; h < numPigeons - 1 - makespan; h++) {
				for (unsigned p = 1; p < numPigeons - makespan; p++) {
					for (unsigned j = 0; j < p; j++) {
					//carj::ScopedTimer timer((*solves.rbegin())["time"]);
					//LOG(INFO) << "P(" << sn - makespan << ", " << p << ", " << h << ")";
					//LOG(INFO) << "P(" << sn - makespan << ", " << j << ", " << h << ")";
					solver.assume(P(sn - makespan, p, h));
					solver.assume(P(sn - makespan, j, h));
					bool solved = (solver.solve() == ipasir::SolveResult::SAT);
					assert(!solved);
					}
				}
			}
		}


		for (unsigned p = 0; p < numPigeons; p++) {
			addClause({H(p,0)});
			addClause({-H(p, numPigeons - 1)});
		}

		auto& solves = carj::getCarj()
			.data["/incphp/result/solves"_json_pointer];
		solves.clear();
		for (unsigned makespan = 0; makespan < numPigeons - 1; makespan++) {
			solves.push_back({
				{"makespan", makespan},
				{"time", -1}
			});
			LOG(INFO) << "Makespan: " << makespan;
			carj::ScopedTimer timer((*solves.rbegin())["time"]);

			int h = numPigeons - 2 - makespan;
			//int h = makespan;
			// each pigeon has at least one hole
			for (unsigned p = 0; p < numPigeons; p++) {
				addClause({
					-H(p, h),
					P(sn, p, h),
					H(p, h + 1)
				});
			}

			for (unsigned p = 0; p < numPigeons; p++) {
				// learn at least one
				for (unsigned ms = 0; ms < makespan; ms++) {
					for (unsigned h2 = h; h2 < numPigeons - 1 - ms; h2++) {
						//carj::ScopedTimer timer((*solves.rbegin())["time"]);
						//LOG(INFO) << "P(" << sn - makespan << ", " << p << ", " << h << ")";
						//LOG(INFO) << "P(" << sn - makespan << ", " << j << ", " << h << ")";
						solver.assume(-P(sn - ms, p, h2));
					}
					for (unsigned p2 = 0; p2 < numPigeons; p2++) {
						solver.assume(H(p2,h));
					}

					bool solved = (solver.solve() == ipasir::SolveResult::SAT);
					assert(!solved);
				}
				//solver.assume(H(p,h));
				//solver.assume(-H(p,h + 1));
			}

			// bool solved = (solver.solve() == ipasir::SolveResult::SAT);
			// assert(!solved);

			// // learn at least one
			// for (unsigned p = 1; p < numPigeons - makespan; p++) {
			// 	for (unsigned h = 0; h < numPigeons - 1 - makespan; h++) {
			// 		//carj::ScopedTimer timer((*solves.rbegin())["time"]);
			// 		//LOG(INFO) << "P(" << sn - makespan << ", " << p << ", " << h << ")";
			// 		//LOG(INFO) << "P(" << sn - makespan << ", " << j << ", " << h << ")";
			// 		solver.assume(-P(sn - makespan, p, h));
			// 	}
			// 	bool solved = (solver.solve() == ipasir::SolveResult::SAT);
			// 	assert(!solved);
			// }
		}

		LOG(INFO) << "Final solve";
		bool solved = (solver.solve() == ipasir::SolveResult::SAT);
		assert(!solved);
		solved = (solver.solve() == ipasir::SolveResult::SAT);
		assert(!solved);
	}

private:
	ipasir::Solver solver;
	unsigned numPigeons;

	SatVariableAllocator allocator;
	SatVariable<unsigned, unsigned> H;
	SatVariable<unsigned, unsigned, unsigned> P;

	void addClause(std::vector<int> clause) {
		for (int literal: clause) {
			solver.add(literal);
		}
		solver.add(0);
	}
};

carj::TCarjArg<TCLAP::ValueArg, unsigned> numberOfPigeons("n", "numPigeons",
	"Number of pigeons", !neccessaryArgument, 1, "natural number", cmd);

carj::CarjArg<TCLAP::SwitchArg, bool> dimspec("d", "dimspec", "Output dimspec.",
	cmd, defaultIsFalse);

carj::CarjArg<TCLAP::SwitchArg, bool> print("p", "print", "Output as cnf.",
	cmd, defaultIsFalse);

carj::CarjArg<TCLAP::SwitchArg, bool> extendedResolution("e", "extendedResolution",
	"Add extended resolution formulas.", cmd, defaultIsFalse);

carj::CarjArg<TCLAP::SwitchArg, bool> incremental("i", "incremental",
	"Solve formual incrementally.", cmd, defaultIsFalse);

carj::CarjArg<TCLAP::SwitchArg, bool> encoding3SAT("3", "3sat",
	"Encode PHP in 3 SAT CNF.", cmd, defaultIsFalse);

int incphp_main(int argc, const char **argv) {
	carj::init(argc, argv, cmd, "/incphp/parameters");

	if (dimspec.getValue()) {
		DimSpecFixedPigeons dsfp(numberOfPigeons.getValue());
		dsfp.print();
	} else {
		std::unique_ptr<ipasir::Ipasir> solver;
		if (print.getValue()) {
			solver = std::make_unique<ipasir::Printer>();
		} else {
			solver = std::make_unique<ipasir::Solver>();
		}

		if (encoding3SAT.getValue()) {
			if (extendedResolution.getValue()) {
				ExtendedPHPEncoder3SAT encoder(
					std::move(solver),
					numberOfPigeons.getValue());
				if (incremental.getValue()) {
					encoder.solveIncremental();
				} else {
					encoder.solve();
				}
			} else {
				PHPEncoder3SAT encoder(
					std::move(solver),
					numberOfPigeons.getValue());
				if (incremental.getValue()) {
					encoder.solveIncremental();
				} else {
					encoder.solve();
				}
			}
		} else {
			if (extendedResolution.getValue()) {
				LOG(FATAL) << "Unsupported Option";
			}

			if (incremental.getValue()) {
				SimpleIncrementalPHPEncoder encoder(
					std::move(solver),
					numberOfPigeons.getValue());
				encoder.solve();
			} else {
				UniversalPHPEncoder encoder(
					std::move(solver),
					numberOfPigeons.getValue());
				encoder.solve();
			}
		}
	}

	return 0;
}
