#include "ipasir/ipasir_cpp.h"
#include "carj/carj.h"
#include "carj/logging.h"

#include <iostream>

class LearnedClauseEvaluationDecorator: public ipasir::Ipasir {
public:

	LearnedClauseEvaluationDecorator(std::unique_ptr<Ipasir> _solver = std::make_unique<ipasir::Solver>()):
			solver(std::move(_solver)) {
		init();
	}

	virtual ~LearnedClauseEvaluationDecorator(){
		LOG(INFO) << numLearnedClausesWithAssumedLiteral;
		LOG(INFO) << numLearnedClauses;
		LOG(INFO) << numSolvesWithAssumptionFound;
		LOG(INFO) << numSolvesWithSubsetAssumptionFound;
		LOG(INFO) << numSolvesWithAssumption;

		if (numLearnedClauses > 0)
			LOG(INFO) << "usless clauses: " << static_cast<float>(numLearnedClausesWithAssumedLiteral)/ numLearnedClauses * 100 << "%";

		if (numSolvesWithAssumption > 0) {
			LOG(INFO) << "assumption learned: " << static_cast<float>(numSolvesWithAssumptionFound)/ numSolvesWithAssumption * 100 << "%";
			LOG(INFO) << "subset of assumption learned: " << static_cast<float>(numSolvesWithSubsetAssumptionFound)/ numSolvesWithAssumption * 100 << "%";
		}
	}

	virtual std::string signature(){
		return solver->signature();
	};

	virtual void add(int lit_or_zero) {
		solver->add(lit_or_zero);
	}

	virtual void assume(int lit) {
		solver->assume(lit);
		// std::cout << lit << " ";
		assumedClause.insert(-lit);
	}

	virtual int val(int lit) {
		return solver->val(lit);
	};

	virtual int failed (int lit) {
		return solver->failed(lit);
	};

	virtual void set_learn(int max_length, std::function<void(int*)> callback) {
		this->learnedClauseCallback = callback;
		this->max_length = max_length;
	}

	virtual ipasir::SolveResult solve() {
		// std::cout << std::endl << "learned:" << std::endl;
		this->foundAssumed = false;
		this->foundSubsetAssumed = false;
		auto result = solver->solve();
		if (this->assumedClause.size() > 0) {
			this->numSolvesWithAssumption += 1;
			if (this->foundAssumed) {
				this->numSolvesWithAssumptionFound += 1;
			}
			if (this->foundSubsetAssumed) {
				this->numSolvesWithSubsetAssumptionFound += 1;
			}
		}

		this->assumedClause.clear();
		this->updateLoggedData();
		return result;
	}

	virtual void set_terminate (std::function<int(void)> callback) {
		solver->set_terminate(callback);
	};

	virtual void reset() {
		solver->reset();
		init();
	};

	virtual void init() {
		max_length = 0;

		numLearnedClauses = 0;
		numLearnedClausesWithAssumedLiteral = 0;

		foundAssumed = 0;
		numSolvesWithAssumption = 0;
		numSolvesWithAssumptionFound = 0;
		numSolvesWithSubsetAssumptionFound = 0;

		solver->set_learn(
			10000,
			std::bind(
				&LearnedClauseEvaluationDecorator::learnedClauseEval,
				this,
				std::placeholders::_1));
	}

	virtual void learnedClauseEval(int* learned) {
		int* clause = learned;
		std::set<int> learnedLiterals;
		bool counted = false;
		bool subsetOfAssumed = true;
		this->numLearnedClauses += 1;
		for (;*learned != 0; learned++) {
			// std::cout << *learned << " ";
			learnedLiterals.insert(*learned);
			if (assumedClause.find(*learned) != assumedClause.end()) {
				if (!counted) {
					counted = true;
					this->numLearnedClausesWithAssumedLiteral += 1;
				}
			} else {
				subsetOfAssumed = false;
			}
		}
		// std::cout << std::endl;

		this->foundAssumed |= (learnedLiterals == assumedClause);
		this->foundSubsetAssumed |= subsetOfAssumed;

		if (learnedLiterals.size() <= static_cast<unsigned>(this->max_length)){
			learnedClauseCallback(clause);
		}
	}

private:
	std::unique_ptr<Ipasir> solver;
	std::set<int> assumedClause;
	int max_length;
	std::function<void(int*)> learnedClauseCallback;

	unsigned numLearnedClauses;
	unsigned numLearnedClausesWithAssumedLiteral;

	bool foundAssumed;
	bool foundSubsetAssumed;
	unsigned numSolvesWithAssumption;
	unsigned numSolvesWithAssumptionFound;
	unsigned numSolvesWithSubsetAssumptionFound;

	void updateLoggedData(){
		static auto& solves = carj::getCarj()
			.data["/incphp/result/solves"_json_pointer];

		if (solves.size() > 0) {
			solves.back()["numLearnedClauses"] = numLearnedClauses;
			solves.back()["numLearnedClausesWithAssumedLiteral"] = numLearnedClausesWithAssumedLiteral;
			solves.back()["numSolvesWithAssumption"] = numSolvesWithAssumption;
			solves.back()["numSolvesWithAssumptionFound"] = numSolvesWithAssumptionFound;
			solves.back()["numSolvesWithSubsetAssumptionFound"] = numSolvesWithSubsetAssumptionFound;
		}

		static auto& global = carj::getCarj()
			.data["/incphp/result/learnedClauseEval"_json_pointer];
		global["numLearnedClauses"] = numLearnedClauses;
		global["numLearnedClausesWithAssumedLiteral"] = numLearnedClausesWithAssumedLiteral;
		global["numSolvesWithAssumption"] = numSolvesWithAssumption;
		global["numSolvesWithAssumptionFound"] = numSolvesWithAssumptionFound;
		global["numSolvesWithSubsetAssumptionFound"] = numSolvesWithSubsetAssumptionFound;
	}
};
