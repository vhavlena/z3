#ifndef _NOODLER_REGEX_H_
#define _NOODLER_REGEX_H_

#include <functional>
#include <list>
#include <set>
#include <stack>
#include <map>
#include <memory>
#include <queue>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "smt/params/smt_params.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "smt/params/theory_str_params.h"
#include "smt/smt_kernel.h"
#include "smt/smt_theory.h"
#include "smt/smt_arith_value.h"
#include "util/scoped_vector.h"
#include "util/union_find.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"

#include "formula.h"
#include "util.h"
#include "aut_assignment.h"

// FIXME most if not all these functions should probably be in theory_str_noodler

namespace smt::noodler::regex {
    using expr_pair = std::pair<expr_ref, expr_ref>;
    using expr_pair_flag = std::tuple<expr_ref, expr_ref, bool>;

    /**
     * @brief Info gathered about a regex. 
     * - min_length: length of shortest words in the regex. In fact it expresses that in the regex there is no 
     *      word shorter than min_length. It does not mean that regex contains a word of length exactly min_length. 
     *      If empty == l_true or l_undef, this values is not valid. 
     * - universal: is regex universal?
     * - empty: is regex empty?
     */
    struct RegexInfo {
        unsigned min_length;
        lbool universal;
        lbool empty;
    };

     /**
     * Extract symbols from a given expression @p ex. Append to the output parameter @p alphabet.
     * @param[in] ex Expression to be checked for symbols.
     * @param[in] m_util_s Seq util for AST.
     * @param[in] m AST manager.
     * @param[out] alphabet A set of symbols with where found symbols are appended to.
     */
    void extract_symbols(expr * ex, const seq_util& m_util_s, const ast_manager& m, std::set<uint32_t>& alphabet);

    /**
     * Convert expression @p expr to NFA using hexadecimal values as symbols.
     * @param[in] expression Expression to be converted to regex.
     * @param[in] m_util_s Seq util for AST.
     * @param[in] m AST manager.
     * @param[in] alphabet Alphabet to be used in re.allchar (SMT2: '.') expressions.
     * @param[in] determinize Determinize intermediate automata
     * @param[in] make_complement Whether to make complement of the passed @p expr instead.
     * @return The resulting regex.
     */
    [[nodiscard]] Mata::Nfa::Nfa conv_to_nfa(const app *expression, const seq_util& m_util_s, const ast_manager& m,
                                             const std::set<uint32_t>& alphabet, bool determinize = false, bool make_complement = false);

    /**
     * Create NFA accepting a word in Z3 zstring representation.
     * @param word Word to accept.
     * @return NFA.
     */
    Mata::Nfa::Nfa create_word_nfa(const zstring& word);

    /**
     * @brief Get basic information about the regular expression in the form of RegexInfo (see the description above). 
     * RegexInfo gathers information about emptiness; universality; length of shortest words
     * 
     * @param expression Regex to be checked
     * @param m_util_s string ast util
     * @param m ast manager
     * @return RegexInfo 
     */
    RegexInfo get_regex_info(const app *expression, const seq_util& m_util_s, const ast_manager& m);
}

#endif
