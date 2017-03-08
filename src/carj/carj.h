#include "tclap/CmdLine.h"

namespace carj {
	TCLAP::CmdLine& getCmd();

	void init(int argc, const char **argv) {
		std::array<const char*, 2> argv_help = {argv[0], "-h"};
		if (argc == 1) {
			argc = 2;
			argv = argv_help.data();
		}
		carj::getCmd().parse( argc, argv );
	}
}
