#pragma once

#include "logging.h"

#include "tclap/CmdLine.h"
#include "json.hpp"

#include <iostream>
#include <fstream>
#include <string>
#include <vector>

namespace carj {
	using json = nlohmann::json;

	class Carj;
	class CarjArgBase;

	Carj& getCarj();
	std::vector<CarjArgBase*>& getArgs();

	void init(int argc, const char **argv, TCLAP::CmdLine& cmd);

	class Carj {
	public:
		const std::string configPath = "carj.json";

		Carj(bool loadFromDefault = false) {
			if (loadFromDefault) {
				std::ifstream inStream(configPath);
				if (inStream) {
					inStream >> data;
				}
			}
		}

		~Carj(){
			std::ofstream o(configPath);
			o << std::setw(4) << data << std::endl;
		}

		json data;
	};

	class CarjArgBase {
	public:
		CarjArgBase(){
			getArgs().push_back(this);
		}

		virtual ~CarjArgBase(){

		}

		virtual void writeToJson() = 0;

		static void writeAllToJson() {
			for (CarjArgBase* arg: getArgs()) {
				arg->writeToJson();
			}
		}
	};

	template<typename TemplateType, typename ValueType>
	class CarjArgImpl: public CarjArgBase {
	public:
		template<typename ...Args>
		CarjArgImpl(Args&&... params):
			parameter(std::forward<Args>(params)...) {
		}

		virtual ~CarjArgImpl(){

		}

		virtual void writeToJson() {
			auto it = getCarj().data.find(parameter.getName());
			if (it != getCarj().data.end()) {
				if (parameter.isSet()) {
					json old = *it;
					ValueType oldValue = old.get<ValueType>();
					if (oldValue != parameter.getValue()) {
						LOG(WARNING)
							<< "Overwriting setting in config file for parameter "
							<< parameter.getName()
							<< ".";

						LOG(INFO)
							<< "old setting: " << oldValue
							<< " new setting: " << parameter.getValue();
					}
					getCarj().data[parameter.getName()] = parameter.getValue();
				}
			} else {
				getCarj().data[parameter.getName()] = parameter.getValue();
			}
		}

		ValueType getValue(){
			ValueType value = parameter.getValue();
			try
			{
				// the value is contained in the json file (as we write back
				// parameters to the json, this is the case for parameters)
				json a = getCarj().data.at(parameter.getName());
				try {
					value = a.get<ValueType>();
				} catch (std::domain_error& e) {
					LOG(ERROR) << "Configuration File invalid. "
						<< "std::domain_error for "
						<< parameter.getName() << ": "
						<< e.what();
					LOG(WARNING) << "Using default value: "
						<< parameter.getName() << " = " << value;
				}
			}
			catch (std::out_of_range)
			{

			}
			return value;
		}

	private:
		TemplateType parameter;
	};

	template<template <typename Type> class TemplateType, typename ValueType>
	class TCarjArg: public CarjArgImpl<TemplateType<ValueType>, ValueType> {
		public:
			template<typename ...Args>
			TCarjArg(Args&&... params):
				CarjArgImpl<TemplateType<ValueType>, ValueType>(std::forward<Args>(params)...) {
			}
	};

	template<typename TemplateType, typename ValueType>
	class CarjArg: public CarjArgImpl<TemplateType, ValueType> {
		public:
			template<typename ...Args>
			CarjArg(Args&&... params):
				CarjArgImpl<TemplateType, bool>(std::forward<Args>(params)...) {
			}
	};
}
