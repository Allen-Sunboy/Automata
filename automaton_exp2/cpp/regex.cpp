#include "regex.h"

/**
 * 注：如果你愿意，你可以自由的using namespace。
 */

/**
 * 由根节点为Regex的子树，构建自动机，每个子节点是Expression，分别调用compileExpression()函数
 * @param r 子树的根节点，为RegexContext类型
*/
void Regex::compileRegex(regexParser::RegexContext *r)
{
    // 当前的起始状态
    int currentState = nfa.last;
    std::vector<regexParser::ExpressionContext*> expressions = r->expression();

    // 保存每个分支的最末尾状态
    std::vector<int> stateList;
    for(auto e: expressions)
    {
        // 对于每个分支，先新建一个状态，再连接这个分支
        Rule tmp;
        tmp.dst = nfa.num_states;
        tmp.type = EPSILON;
        nfa.rules[currentState].push_back(tmp);

        nfa.last = nfa.num_states;
        nfa.num_states++;

        compileExpression(e);
        stateList.push_back(nfa.last);
    }

    for(int i = 0; i < stateList.size(); i++)
    {
        // 新建一个状态，将这多条分支的最末尾状态汇总到这个状态
        Rule tmp;
        tmp.dst = nfa.num_states;
        tmp.type = EPSILON;
        nfa.rules[stateList[i]].push_back(tmp);
    }
    // 更新
    nfa.last = nfa.num_states;
    nfa.num_states++;

}

/**
 * 由根节点为Expression的子树，构建自动机，每个子节点是ExpressionItem，分别调用compileExpressionItem()函数
 * @param e 子树的根节点，为ExpressionContext类型
*/
void Regex::compileExpression(regexParser::ExpressionContext *e)
{
    std::vector<regexParser::ExpressionItemContext*> expressionItems = e->expressionItem();

    for(auto ei: expressionItems)
    {
        compileExpressionItem(ei);

        // 新建一个状态，作为下一个状态的开头，将上一个状态末尾接到这个状态
        Rule tmp;
        tmp.dst = nfa.num_states;
        tmp.type = EPSILON;

        // 在此处判断是否为贪婪匹配，如果nfa.last != nfa.num_states-1，则为非贪婪匹配，这条规则插入到最前面，否则放在最后面
        if(nfa.last != nfa.num_states-1)
            nfa.rules[nfa.last].insert(nfa.rules[nfa.last].begin(), tmp);
        else
            nfa.rules[nfa.last].push_back(tmp);
        nfa.last = nfa.num_states;
        nfa.num_states++;
    }
}

/**
 * 由根节点为ExpressionItem的子树，构建自动机，如果子节点是single，则调用compileSingle()函数，如果是group，则调用compileRegex()函数
 * @param ei 子树的根节点，为ExpressionItemContext类型
*/
void Regex::compileExpressionItem(regexParser::ExpressionItemContext *ei)
{
    regexParser::NormalItemContext *ni = ei->normalItem();
    regexParser::QuantifierContext *q = ei->quantifier();

    // 当前的起始状态
    int currentState = nfa.last;

    /**
     * 对于有quantifier限定符的处理，需要对相应的自动机进行处理，在外围添加其他epsilon转移。
     * tmp1 在当前最开始的状态后接一个状态，作为该部分自动机的开头
     * tmp2 在该部分自动机的末尾后接一个状态
     * tmp3 将最开始的状态直接跨过该自动机，连接到最后那个状态
     * tmp4 将最后那个状态返回指向最开始的状态
     * 参考了实验二讲解pdf的思路
     * 对于贪婪匹配与否的处理，主要就是这些规则添加的先后顺序
     * 需要注意的是，由于我nfa路径访问是使用DFS栈处理，同一状态发出的规则，越后面的规则越晚入栈，从而越靠近栈顶，越先访问到
     * 所以是根据这种情况进行的处理
    */
    if(q != nullptr)
    {
        // 贪婪匹配
        if(!q->lazyModifier())
        {
            int end = nfa.num_states;

            // 直接跨过该部分自动机
            Rule tmp3;
            tmp3.dst = end;
            tmp3.type = EPSILON;

            // 返回最开始的状态
            Rule tmp4;
            tmp4.dst = currentState;
            tmp4.type = EPSILON;

            if(q->quantifierType()->ZeroOrOneQuantifier())
            {
                nfa.rules[currentState].push_back(tmp3);
            }


            else if(q->quantifierType()->ZeroOrMoreQuantifier())
            {
                nfa.rules[currentState].push_back(tmp3);
                nfa.rules[end].push_back(tmp4);
            }

            // OneOrMore
            else
            {
                nfa.rules[end].push_back(tmp4);
            }

            // 上述过程新建了2个状态
            nfa.num_states += 2;
            nfa.last = nfa.num_states-1;

            if(ni->single())
                compileSingle(ni->single());
            else
                compileRegex(ni->group()->regex());

            // 新建一个状态，连在最开始的状态后面，作为该部分自动机的开头
            Rule tmp1;
            tmp1.dst = end+1;
            tmp1.type = EPSILON;
            nfa.rules[currentState].push_back(tmp1);

            // 新建一个状态，将该自动机的末尾连接到这个状态
            Rule tmp2;
            tmp2.dst = end;
            tmp2.type = EPSILON;
            nfa.rules[nfa.last].push_back(tmp2);

            nfa.last = end;

        }
        // lazy，非贪婪匹配
        else
        {
            // 新建一个状态，连在最开始的状态后面，作为该部分自动机的开头
            Rule tmp1;
            tmp1.dst = nfa.num_states;
            tmp1.type = EPSILON;
            nfa.rules[currentState].push_back(tmp1);

            nfa.last = nfa.num_states;
            nfa.num_states++;

            if(ni->single())
                compileSingle(ni->single());
            else
                compileRegex(ni->group()->regex());

            // 新建一个状态，将该自动机的末尾连接到这个状态
            Rule tmp2;
            tmp2.dst = nfa.num_states;
            tmp2.type = EPSILON;
            nfa.rules[nfa.last].push_back(tmp2);

            nfa.last = nfa.num_states;
            nfa.num_states++;
            

            // 直接跨过该部分自动机
            Rule tmp3;
            tmp3.dst = nfa.num_states-1;
            tmp3.type = EPSILON;

            // 返回最开始的状态
            Rule tmp4;
            tmp4.dst = currentState;
            tmp4.type = EPSILON;

            if(q->quantifierType()->ZeroOrOneQuantifier())
            {
                nfa.rules[currentState].push_back(tmp3);
            }


            else if(q->quantifierType()->ZeroOrMoreQuantifier())
            {
                nfa.rules[currentState].push_back(tmp3);
                nfa.rules[nfa.num_states-1].push_back(tmp4);
            }

            // OneOrMore
            else
            {
                nfa.rules[nfa.num_states-1].push_back(tmp4);
            }

        }
    }

    else
    {
        if(ni->single())
            compileSingle(ni->single());
        else
            compileRegex(ni->group()->regex());
    }

    
}

/**
 * 由根节点为Single的子树，构建自动机，新建一条Rule，根据子节点的类型，设置其type和by等内容
 * @param s 子树的根节点，为SingleContext类型
*/

void Regex::compileSingle(regexParser::SingleContext *s)
{
    Rule tmp;
    tmp.dst = nfa.num_states;
    if(s->char_())
    {
        tmp.type = NORMAL;
        if(s->char_()->EscapedChar())
            tmp.by = s->getText().substr(1, 1);
        else
            tmp.by = s->getText();
    }

    else if(s->characterClass())
    {
        tmp.type = SPECIAL;
        tmp.by = s->getText().substr(1, 1);
    }

    else if(s->AnyCharacter())
    {
        tmp.type = SPECIAL;
        tmp.by = s->getText();
    }

    // CharacterGroup
    else
    {
        tmp.type = GROUP;

        std::vector<regexParser::CharacterGroupItemContext*> characterGroupitems = s->characterGroup()->characterGroupItem();
        if(characterGroupitems.empty())
        {
            nfa.last = nfa.num_states;
            nfa.num_states++;
            return;
        }

        if(s->characterGroup()->characterGroupNegativeModifier())
            for(int i = 0; i < 129; i++)
                tmp.in[i] = 1;
        else
            for(int i = 0; i < 129; i++)
                tmp.in[i] = 0;

        for(auto i: characterGroupitems)
        {
            if(i->charInGroup())
            {
                char a;
                if(i->getText().length() > 1)
                    a = i->getText().data()[1];
                else
                    a = i->getText().data()[0];
                tmp.in[a] = !tmp.in[a];
            }

            else if(i->characterClass())
            {
                if(i->characterClass()->CharacterClassAnyWord())
                {
                    for(int j = 0; j < 129; j++)
                        if((j >= 'a' && j <= 'z') || (j >= 'A' && j <= 'Z') || (j >= '0' && j <= '9') || j == '_')
                            tmp.in[j] = !tmp.in[j];
                }

                else if(i->characterClass()->CharacterClassAnyWordInverted())
                {
                    for(int j = 0; j < 129; j++)
                        if(!((j >= 'a' && j <= 'z') || (j >= 'A' && j <= 'Z') || (j >= '0' && j <= '9') || j == '_'))
                            tmp.in[j] = !tmp.in[j];
                }

                else if(i->characterClass()->CharacterClassAnyDecimalDigit())
                {
                    for(int j = 0; j < 129; j++)
                        if(j >= '0' && j <= '9')
                            tmp.in[j] = !tmp.in[j];
                }

                else if(i->characterClass()->CharacterClassAnyDecimalDigitInverted())
                {
                    for(int j = 0; j < 129; j++)
                        if(!(j >= '0' && j <= '9'))
                            tmp.in[j] = !tmp.in[j];
                }

                else if(i->characterClass()->CharacterClassAnyBlank())
                {
                    for(int j = 0; j < 129; j++)
                        if(j == ' ' || j == '\f' || j == '\n' || j == '\r' || j == '\t' || j == '\v')
                            tmp.in[j] = !tmp.in[j];
                }

                // CharacterClassAnyBlankInverted
                else
                {
                    for(int j = 0; j < 129; j++)
                        if(!(j == ' ' || j == '\f' || j == '\n' || j == '\r' || j == '\t' || j == '\v'))
                            tmp.in[j] = !tmp.in[j];
                }
            }

            //characterRange
            else
            {
                char start = i->characterRange()->charInGroup(0)->getText().data()[0];
                char end = i->characterRange()->charInGroup(1)->getText().data()[0];

                for(int j = (int)start; j <= (int)end; j++)
                    tmp.in[j] = !tmp.in[j];
            }
        }

    }

    nfa.rules[nfa.last].push_back(tmp);
    nfa.last = nfa.num_states;
    nfa.num_states++;

}


/**
 * 编译给定的正则表达式。
 * 具体包括两个过程：解析正则表达式得到语法分析树（这步已经为你写好，即parse方法），
 * 和在语法分析树上进行分析（遍历），构造出NFA（需要你完成的部分）。
 * 在语法分析树上进行分析的方法，可以是直接自行访问该树，也可以是使用antlr的Visitor机制，详见作业文档。
 * 你编译产生的结果，NFA应保存在当前对象的nfa成员变量中，其他内容也建议保存在当前对象下（你可以自由地在本类中声明新的成员）。
 * @param pattern 正则表达式的字符串
 * @param flags 正则表达式的修饰符（第二次实验不要求支持，保证传入的永远是空串）
 */
void Regex::compile(const std::string &pattern, const std::string &flags) {
    regexParser::RegexContext *tree = Regex::parse(pattern); // 这是语法分析树
    // TODO 请你完成这个函数
    // 你应该根据tree中的内容，恰当地构造NFA
    // 构造好的NFA，和其他数据变量（如有），均建议保存在当前对象中。
    // 例如 (this->)nfa.num_states = 100;

    // 起始状态编号为0，即初态
    nfa.last = 0;
    nfa.num_states = 1;

    nfa.rules.resize(50000);

    // 递归的入口，从根节点开始，递归构建自动机
    compileRegex(tree);

    nfa.rules.resize(nfa.num_states);

    nfa.is_final.resize(nfa.num_states);
    nfa.is_final[nfa.num_states-1] = 1;

    //test
    // for(int i = 0; i < nfa.num_states; i++)
    //     for(auto j: nfa.rules[i])
    //         std::cerr << i << " " << j.dst << " " << j.type << " " << j.by << std::endl;
    
}

/**
 * 在给定的输入文本上，进行正则表达式匹配，返回匹配到的第一个结果。
 * 匹配不成功时，返回空vector( return std::vector<std::string>(); ，或使用返回初始化列表的语法 return {}; )；
 * 匹配成功时，返回一个std::vector<std::string>，其中下标为0的元素是匹配到的字符串，
 * 下标为i(i>=1)的元素是匹配结果中的第i个分组。
 * （第二次实验中不要求支持分组功能，返回的vector中只含一个元素即可）
 * @param text 输入的文本
 * @return 如上所述
 */
std::vector<std::string> Regex::match(std::string text) {
    // TODO 请你完成这个函数
    std::vector<std::string> result;

    int len = text.length();
    for(int i = 0; i < len; i++)
    {
        std::string temp = text.substr(i, len-i);
        Path path = nfa.exec(temp);
        
        if(!path.states.empty())
        {
            std::string str;
            for(int i = 0; i < path.consumes.size(); i++)
                str.append(path.consumes[i]);
            result.push_back(str);

            return result;
        }
    }

    return {};
}

/**
 * 解析正则表达式的字符串，生成语法分析树。
 * 你应该在compile函数中调用一次本函数，以得到语法分析树。
 * 通常，你不需要改动此函数，也不需要理解此函数实现每一行的具体含义。
 * 但是，你应当对语法分析树的数据结构(RegexContext)有一定的理解，作业文档中有相关的教程可供参考。
 * @param pattern 要解析的正则表达式的字符串
 * @return RegexContext类的对象的指针。保证不为空指针。
 */
regexParser::RegexContext *Regex::parse(const std::string &pattern) {
    if (antlrInputStream) throw std::runtime_error("此Regex对象已被调用过一次parse函数，不可以再次调用！");
    antlrInputStream = new antlr4::ANTLRInputStream(pattern);
    antlrLexer = new regexLexer(antlrInputStream);
    antlrTokenStream = new antlr4::CommonTokenStream(antlrLexer);
    antlrParser = new regexParser(antlrTokenStream);
    regexParser::RegexContext *tree = antlrParser->regex();
    if (!tree) throw std::runtime_error("parser解析失败(函数返回了nullptr)");
    auto errCount = antlrParser->getNumberOfSyntaxErrors();
    if (errCount > 0) throw std::runtime_error("parser解析失败，表达式中有" + std::to_string(errCount) + "个语法错误！");
    if (antlrTokenStream->LA(1) != antlr4::Token::EOF)
        throw std::runtime_error("parser解析失败，解析过程未能到达字符串结尾，可能是由于表达式中间有无法解析的内容！已解析的部分："
                                 + antlrTokenStream->getText(antlrTokenStream->get(0),
                                                             antlrTokenStream->get(antlrTokenStream->index() - 1)));
    return tree;
}

// 此析构函数是为了管理ANTLR语法分析树所使用的内存的。你不需要阅读和理解它。
Regex::~Regex() {
    delete antlrInputStream;
    delete antlrLexer;
    delete antlrTokenStream;
    delete antlrParser;
}
