#include "carj.h"

TCLAP::SwitchArg useConfig("", "useConfig",
	"Use configuration file 'carj.json'.",
	/*default*/ false);

carj::Carj& carj::getCarj() {
	static carj::Carj carj(useConfig.getValue());
	return carj;
}

std::vector<carj::CarjArgBase*>& carj::getArgs(){
	static std::vector<carj::CarjArgBase*> args;
	return args;
}

void initLogger(){
	el::Configurations conf;
	conf.setToDefault();
	conf.setGlobally(el::ConfigurationType::Format, "ci %level %fbase:%line; %msg");
	conf.set(el::Level::Fatal, el::ConfigurationType::Format, "%level %fbase:%line; %msg");
	el::Loggers::reconfigureAllLoggers(conf);

	conf.setGlobally(el::ConfigurationType::Format, "ci %level %datetime{%H:%m:%s}; %msg");
	el::Loggers::reconfigureLogger("performance", conf);
	el::Loggers::setVerboseLevel(2);
}

void carj::init(int argc, const char **argv, TCLAP::CmdLine& cmd) {
	START_EASYLOGGINGPP(argc, argv);
	initLogger();

	std::array<const char*, 2> argv_help = {argv[0], "-h"};
	if (argc == 1) {
		argc = 2;
		argv = argv_help.data();
	}
	cmd.add(useConfig);
	cmd.parse( argc, argv );
	carj::CarjArgBase::writeAllToJson();
}