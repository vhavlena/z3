#include "counter_automaton.h"

namespace std {
    std::ostream& operator<<(std::ostream& out_stream, const smt::noodler::ca::TagSet& tag_set) {
        out_stream << "{";
        for (const auto& tag: tag_set) {
            out_stream << tag.to_string() << ", ";
        }
        out_stream << "}";
        return out_stream;
    }
}