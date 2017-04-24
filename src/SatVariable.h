#include <vector>
#include <initializer_list>
#include <cstddef>
#include <cassert>

template<class ... Types>
class SatVariable {
public:
    int operator()(Types ... args) {
        return operator()({args...});
    }

    int operator()(std::initializer_list<unsigned> _values){
        std::vector<unsigned> values(_values);
        assert(values.size() == dimensions.size());
        for (std::size_t i = 0; i < values.size(); i++) {
            assert(0 <= values[i]);
            assert(values[i] < dimensions[i]);
        }

        unsigned result = 0;
        for (std::size_t i = 0; i < values.size(); i++) {
            result *= dimensions[i];
            result += values[i];
        }
        result += start;

        assert(start <= result);
        assert(result < start + numberOfVariables());
        return result;
    }

private:
    friend class SatVariableAllocator;

    SatVariable(unsigned _start, std::vector<unsigned> _dimensions):
        dimensions(_dimensions), start(_start) {
            assert(start > 0);
    }

    unsigned numberOfVariables() {
        unsigned result = 1;

        for (unsigned dim: dimensions) {
            result *= dim;
        }

        return result;
    }

    std::vector<unsigned> dimensions;
    unsigned start;
};

class SatVariableAllocator {
public:
    SatVariableAllocator() {
        firstUnusedValue = 1;
    }

    template<class ... Types>
    SatVariable<Types...> newVariable(Types ... args) {
        return newVariable<Types...>({args...});
    }

    template<class ... Types>
    SatVariable<Types...> newVariable(std::initializer_list<unsigned> _dimensions) {
        std::vector<unsigned> dimensions(_dimensions);
        SatVariable<Types...> variable = SatVariable<Types...>(firstUnusedValue, dimensions);
        firstUnusedValue += variable.numberOfVariables();
        return variable;
    }

private:
    int firstUnusedValue;
};
