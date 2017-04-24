#include "gtest/gtest.h"
#include "SatVariable.h"

#include <set>

TEST( SatVariable, basic) {
    for (unsigned i = 1; i < 10; i++) {
        for (unsigned j = 1; j < 10; j++) {
            for (unsigned k = 1; k < 10; k++) {
                SatVariableAllocator sva;
                std::set<int> test;
                auto two = sva.newVariable(i,j);
                auto three = sva.newVariable(i,j,k);
                auto one = sva.newVariable(i);

                for (unsigned ip = 0; ip < i; ip++) {
                    auto insertResult = test.insert(one(ip));
                    ASSERT_TRUE(insertResult.second);
                    for (unsigned jp = 0; jp < j; jp++) {
                        insertResult = test.insert(two(ip,jp));
                        ASSERT_TRUE(insertResult.second);
                        for (unsigned kp = 0; kp < k; kp++) {
                            insertResult = test.insert(three(ip,jp,kp));
                            ASSERT_TRUE(insertResult.second);
                        }
                    }
                }

            }
        }
    }
}
