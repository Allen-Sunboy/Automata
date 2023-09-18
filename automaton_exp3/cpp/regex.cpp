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
    int currentState = nfa.num_states-1;
    std::vector<regexParser::ExpressionContext*> expressions = r->expression();

    // 保存每个分支的最末尾状态
    std::vector<int> stateList;
    for(auto e: expressions)
    {
        // 对于每个分支，先新建一个状态，再连接这个分支
        Rule tmp;
        tmp.dst = nfa.num_states;
        tmp.type = EPSILON;
        // nfa.rules[currentState].push_back(tmp);
        nfa.rules[currentState].insert(nfa.rules[currentState].begin(), tmp);

        nfa.num_states++;

        compileExpression(e);
        stateList.push_back(nfa.num_states-1);
        // stateList.insert(stateList.begin(), nfa.num_states-1);
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
    regexParser::AnchorContext *a = ei->anchor();

    // 当前的起始状态
    int currentState = nfa.num_states-1;

    /**
     * 对于有quantifier限定符的处理，需要对相应的自动机进行处理，在外围添加其他epsilon转移。
     * tmp1 在当前最开始的状态后接一个状态，作为该部分item的开头
     * tmp2 在该item的末尾后接一个状态
     * tmp3 将最开始的状态直接跨过该item，连接到最后那个状态
     * tmp4 将最后那个状态返回指向最开始的状态
     * tmp5 连在当前item的末尾，作为下一个item的起点
     * 对于贪婪匹配与否的处理，主要就是这些规则添加的先后顺序
    */
    if(q != nullptr)
    {
        if(q->quantifierType()->rangeQuantifier())
        {
            int p = nfa.group_num;

            if(ni->group())
            {
                if(!ni->group()->groupNonCapturingModifier())
                    nfa.group_num++;
            }

            int lower = std::stoi(q->quantifierType()->rangeQuantifier()->rangeQuantifierLowerBound()->getText());
            for(int i = 0; i < lower; i++)
            {
                int newCurrent = nfa.num_states-1;
                Rule tmp1;
                tmp1.dst = nfa.num_states;
                tmp1.type = EPSILON;

                nfa.rules[newCurrent].push_back(tmp1);
                nfa.num_states++;

                if(ni->single())
                    compileSingle(ni->single());
                else
                {
                    compileRegex(ni->group()->regex());
                    if(!ni->group()->groupNonCapturingModifier())
                        nfa.group[p].push_back(std::make_pair(newCurrent+1, nfa.num_states-1));
                }

                Rule tmp2;
                tmp2.dst = nfa.num_states;
                tmp2.type = EPSILON;

                nfa.rules[nfa.num_states-1].push_back(tmp2);
                nfa.num_states++;
            }

            if(q->quantifierType()->rangeQuantifier()->rangeDelimiter())
            {
                // 相当于后接了 upper-lower 个ZeroOrOne
                if(q->quantifierType()->rangeQuantifier()->rangeQuantifierUpperBound())
                {
                    int upper = std::stoi(q->quantifierType()->rangeQuantifier()->rangeQuantifierUpperBound()->getText());

                    for(int j = lower; j < upper; j++)
                    {
                        int newCurrent = nfa.num_states-1;
                        Rule tmp1;
                        tmp1.dst = nfa.num_states;
                        tmp1.type = EPSILON;

                        nfa.rules[newCurrent].push_back(tmp1);
                        nfa.num_states++;

                        if(ni->single())
                            compileSingle(ni->single());
                        else
                        {
                            compileRegex(ni->group()->regex());
                            if(!ni->group()->groupNonCapturingModifier())
                                nfa.group[p].push_back(std::make_pair(newCurrent+1, nfa.num_states-1));
                        }

                        Rule tmp2;
                        tmp2.dst = nfa.num_states;
                        tmp2.type = EPSILON;

                        nfa.rules[nfa.num_states-1].push_back(tmp2);
                        nfa.num_states++;

                        Rule tmp3;
                        tmp3.dst = nfa.num_states-1;
                        tmp3.type = EPSILON;

                        if(q->lazyModifier())
                            nfa.rules[newCurrent].push_back(tmp3);
                        else
                            nfa.rules[newCurrent].insert(nfa.rules[newCurrent].begin(), tmp3);

                    }

                }

                // 相当于后接了个ZeroOrMore
                else
                {
                    int newCurrent = nfa.num_states-1;
                    Rule tmp1;
                    tmp1.dst = nfa.num_states;
                    tmp1.type = EPSILON;

                    nfa.rules[newCurrent].push_back(tmp1);
                    nfa.num_states++;

                    if(ni->single())
                        compileSingle(ni->single());
                    else
                    {
                        if(!ni->group()->groupNonCapturingModifier())
                            nfa.group_num++;
                        compileRegex(ni->group()->regex());
                        if(!ni->group()->groupNonCapturingModifier())
                            nfa.group[p].push_back(std::make_pair(newCurrent+1, nfa.num_states-1));
                    }

                    Rule tmp2;
                    tmp2.dst = nfa.num_states;
                    tmp2.type = EPSILON;

                    nfa.rules[nfa.num_states-1].push_back(tmp2);
                    nfa.num_states++;

                    Rule tmp3;
                    tmp3.dst = nfa.num_states-1;
                    tmp3.type = EPSILON;

                    Rule tmp4;
                    tmp4.dst = newCurrent;
                    tmp4.type = EPSILON;

                    Rule tmp5;
                    tmp5.dst = nfa.num_states;
                    tmp5.type = EPSILON;
                    nfa.rules[nfa.num_states-1].push_back(tmp5);
                    nfa.num_states++;

                    if(q->lazyModifier())
                    {
                        nfa.rules[newCurrent].push_back(tmp3);
                        nfa.rules[nfa.num_states-2].insert(nfa.rules[nfa.num_states-2].begin(), tmp4);
                    }
                    else
                    {
                        nfa.rules[newCurrent].insert(nfa.rules[newCurrent].begin(), tmp3);
                        nfa.rules[nfa.num_states-2].push_back(tmp4);
                    }
                }
            }
        }

        else
        {
            int p = nfa.group_num;

            Rule tmp1;
            tmp1.dst = nfa.num_states;
            tmp1.type = EPSILON;

            nfa.rules[currentState].push_back(tmp1);
            nfa.num_states++;

            if(ni->single())
                compileSingle(ni->single());
            else
            {
                if(!ni->group()->groupNonCapturingModifier())
                    nfa.group_num++;
                compileRegex(ni->group()->regex());
                if(!ni->group()->groupNonCapturingModifier())
                    nfa.group[p].push_back(std::make_pair(currentState+1, nfa.num_states-1));
            }

            Rule tmp2;
            tmp2.dst = nfa.num_states;
            tmp2.type = EPSILON;

            nfa.rules[nfa.num_states-1].push_back(tmp2);
            nfa.num_states++;

            Rule tmp3;
            tmp3.dst = nfa.num_states-1;
            tmp3.type = EPSILON;

            Rule tmp4;
            tmp4.dst = currentState;
            tmp4.type = EPSILON;

            Rule tmp5;
            tmp5.dst = nfa.num_states;
            tmp5.type = EPSILON;
            nfa.rules[nfa.num_states-1].push_back(tmp5);
            nfa.num_states++;

            if(q->quantifierType()->ZeroOrOneQuantifier())
            {
                // 非贪婪
                if(q->lazyModifier())
                    nfa.rules[currentState].push_back(tmp3);
                // 贪婪
                else
                    nfa.rules[currentState].insert(nfa.rules[currentState].begin(), tmp3);
            }

            else if(q->quantifierType()->ZeroOrMoreQuantifier())
            {
                if(q->lazyModifier())
                {
                    nfa.rules[currentState].push_back(tmp3);
                    nfa.rules[nfa.num_states-2].insert(nfa.rules[nfa.num_states-2].begin(), tmp4);
                }
                else
                {
                    nfa.rules[currentState].insert(nfa.rules[currentState].begin(), tmp3);
                    nfa.rules[nfa.num_states-2].push_back(tmp4);
                }
            }

            // OneOrMore
            else
            {
                if(q->lazyModifier())
                    nfa.rules[nfa.num_states-2].insert(nfa.rules[nfa.num_states-2].begin(), tmp4);
                else
                    nfa.rules[nfa.num_states-2].push_back(tmp4);
            }
        }
    }

    else if(ni != nullptr)
    {
        int p = nfa.group_num;
        std::vector<std::pair<int, int> > g;
        if(ni->single())
            compileSingle(ni->single());
        else
        {
            if(!ni->group()->groupNonCapturingModifier())
                nfa.group_num++;
            compileRegex(ni->group()->regex());
            if(!ni->group()->groupNonCapturingModifier())
                nfa.group[p].push_back(std::make_pair(currentState, nfa.num_states-1));
        }

        Rule tmp5;
        tmp5.dst = nfa.num_states;
        tmp5.type = EPSILON;

        nfa.rules[nfa.num_states-1].push_back(tmp5);
        nfa.num_states++;

    }
    
    // anchor
    else
    {
        Rule tmp;
        tmp.dst = nfa.num_states;
        tmp.type = EPSILON;
        if(a->AnchorStartOfString())
            tmp.by = "^";
        else if(a->AnchorEndOfString())
            tmp.by = "$";
        else if(a->AnchorWordBoundary())
            tmp.by = "b";
        // AnchorNonWordBoundary
        else
            tmp.by = "B";
        
        nfa.rules[currentState].push_back(tmp);
        nfa.num_states++;
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
        {
            if(s->getText().substr(1) == "f")
                tmp.by = "\f";
            else if(s->getText().substr(1) == "n")
                tmp.by = "\n";
            else if(s->getText().substr(1) == "r")
                tmp.by = "\r";
            else if(s->getText().substr(1) == "t")
                tmp.by = "\t";
            else if(s->getText().substr(1) == "v")
                tmp.by = "\v";
            else
                tmp.by = s->getText().substr(1);
        
        }

        else
            tmp.by = s->getText();
    }

    else if(s->characterClass())
    {
        tmp.type = SPECIAL;
        tmp.by = s->getText().substr(1);
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

        // 检测是否有取反
        bool negativeModifier = 0;

        if(s->characterGroup()->characterGroupNegativeModifier())
            negativeModifier = 1;
        
        for(int i = 0; i < 129; i++)
            tmp.in[i] = negativeModifier;

        for(auto i: characterGroupitems)
        {
            if(i->charInGroup())
            {
                char a;
                if(i->charInGroup()->EscapedChar())
                {
                    if(i->getText().substr(1) == "f")
                        a = '\f';
                    else if(i->getText().substr(1) == "n")
                        a = '\n';
                    else if(i->getText().substr(1) == "r")
                        a = '\r';
                    else if(i->getText().substr(1) == "t")
                        a = '\t';
                    else if(i->getText().substr(1) == "v")
                        a = '\v';
                    else
                        a = i->getText().data()[1];
                }
                else
                    a = i->getText().data()[0];
                tmp.in[a] = !negativeModifier;
            }

            else if(i->characterClass())
            {
                if(i->characterClass()->CharacterClassAnyWord())
                {
                    for(int j = 0; j < 129; j++)
                        if((j >= 'a' && j <= 'z') || (j >= 'A' && j <= 'Z') || (j >= '0' && j <= '9') || j == '_')
                            tmp.in[j] = !negativeModifier;
                }

                else if(i->characterClass()->CharacterClassAnyWordInverted())
                {
                    for(int j = 0; j < 129; j++)
                        if(!((j >= 'a' && j <= 'z') || (j >= 'A' && j <= 'Z') || (j >= '0' && j <= '9') || j == '_'))
                            tmp.in[j] = !negativeModifier;
                }

                else if(i->characterClass()->CharacterClassAnyDecimalDigit())
                {
                    for(int j = 0; j < 129; j++)
                        if(j >= '0' && j <= '9')
                            tmp.in[j] = !negativeModifier;
                }

                else if(i->characterClass()->CharacterClassAnyDecimalDigitInverted())
                {
                    for(int j = 0; j < 129; j++)
                        if(!(j >= '0' && j <= '9'))
                            tmp.in[j] = !negativeModifier;
                }

                else if(i->characterClass()->CharacterClassAnyBlank())
                {
                    for(int j = 0; j < 129; j++)
                        if(j == ' ' || j == '\f' || j == '\n' || j == '\r' || j == '\t' || j == '\v')
                            tmp.in[j] = !negativeModifier;
                }

                // CharacterClassAnyBlankInverted
                else
                {
                    for(int j = 0; j < 129; j++)
                        if(!(j == ' ' || j == '\f' || j == '\n' || j == '\r' || j == '\t' || j == '\v'))
                            tmp.in[j] = !negativeModifier;
                }
            }

            //characterRange
            else
            {
                char start = i->characterRange()->charInGroup(0)->getText().data()[0];
                char end = i->characterRange()->charInGroup(1)->getText().data()[0];

                for(int j = (int)start; j <= (int)end; j++)
                    tmp.in[j] = !negativeModifier;
            }
        }
    }

    nfa.rules[nfa.num_states-1].push_back(tmp);
    nfa.num_states++;

}



/**
 * 编译给定的正则表达式。
 * 具体包括两个过程：解析正则表达式得到语法分析树（这步已经为你写好，即parse方法），
 * 和在语法分析树上进行分析（遍历），构造出NFA（需要你完成的部分）。
 * 在语法分析树上进行分析的方法，可以是直接自行访问该树，也可以是使用antlr的Visitor机制，详见作业文档。
 * 你编译产生的结果，NFA应保存在当前对象的nfa成员变量中，其他内容也建议保存在当前对象下（你可以自由地在本类中声明新的成员）。
 * @param pattern 正则表达式的字符串
 * @param flags 正则表达式的修饰符
 */
void Regex::compile(const std::string &pattern, const std::string &flags) {
    regexParser::RegexContext *tree = Regex::parse(pattern); // 这是语法分析树
    // TODO 请你将在上次实验的内容粘贴过来，在其基础上进行修改。

    if(flags.find("m") != std::string::npos)
        nfa.flag_m = 1;
    if(flags.find("s") != std::string::npos)
        nfa.flag_s = 1;

    nfa.num_states = 1;

    nfa.rules.resize(30000);

    // 递归的入口，从根节点开始，递归构建自动机
    compileRegex(tree);

    nfa.rules.resize(nfa.num_states);

    nfa.is_final.resize(nfa.num_states);
    nfa.is_final[nfa.num_states-1] = 1;

    // for(int i = 0; i < nfa.num_states; i++)
    //     for(auto j: nfa.rules[i])
    //         std::cerr << i << " " << j.dst << " " << j.type << " " << j.by << std::endl;
    
}

/**
 * 在给定的输入文本上，进行正则表达式匹配，返回匹配到的第一个结果。
 * 匹配不成功时，返回空vector( return std::vector<std::string>(); ，或使用返回初始化列表的语法 return {}; )；
 * 匹配成功时，返回一个std::vector<std::string>，其中下标为0的元素是匹配到的字符串，
 * 下标为i(i>=1)的元素是匹配结果中的第i个分组。
 * @param text 输入的文本
 * @return 如上所述
 */
std::vector<std::string> Regex::match(std::string text) {
    // TODO 请你将在上次实验的内容粘贴过来，在其基础上进行修改。
    std::vector<std::string> result;

    int len = text.length();

    nfa.p = 0;
    while(nfa.p < len)
    {
        Path path = nfa.exec(text);
        
        if(!path.states.empty())
        {
            std::string str;
            for(int j = 0; j < path.consumes.size(); j++)
                str.append(path.consumes[j]);

            result.push_back(str);

            for(int i = 0; i < nfa.group_num; i++)
            {
                int j = nfa.group[i].size()-1;
                while(j >= 0)
                {
                    int k = path.states.size()-1;
                    while(path.states[k] != nfa.group[i][j].first && k >= 0)
                        k--;
                    if(k < 0)
                        j--;
                    else
                    {
                        int l = k;
                        while(path.states[l] != nfa.group[i][j].second && l < path.states.size())
                            l++;
                        if(l >= path.states.size())
                            j--;
                        else
                        {
                            std::string str0;
                            for(int m = k; m < l; m++)
                                str0.append(path.consumes[m]);
                            result.push_back(str0);
                            break;
                        }
                    }

                }
                if(j < 0)
                {
                    result.push_back("");
                    continue;
                }

            }

            return result;
        }
        else
            nfa.p++;
    }

    return {};
}

/**
 * 在给定的输入文本上，进行正则表达式匹配，返回匹配到的**所有**结果。
 * 匹配不成功时，返回空vector( return std::vector<std::string>(); ，或使用返回初始化列表的语法 return {}; )；
 * 匹配成功时，返回一个std::vector<std::vector<std::string>>，其中每个元素是每一个带分组的匹配结果，其格式同match函数的返回值（详见上面）。
 * @param text 输入的文本
 * @return 如上所述
 */
std::vector<std::vector<std::string>> Regex::matchAll(std::string text) {
    // TODO 请你完成这个函数
    std::vector<std::vector<std::string>> result;

    int len = text.length();

    nfa.p = 0;
    while(nfa.p < len)
    {
        std::vector<std::string> temp;

        Path path = nfa.exec(text);
        if(!path.states.empty())
        {
            std::string str;
            for(int j = 0; j < path.consumes.size(); j++)
                str.append(path.consumes[j]);
            temp.push_back(str);

            for(int i = 0; i < nfa.group_num; i++)
            {
                int j = nfa.group[i].size()-1;
                while(j >= 0)
                {
                    int k = path.states.size()-1;
                    while(path.states[k] != nfa.group[i][j].first && k >= 0)
                        k--;
                    if(k < 0)
                        j--;
                    else
                    {
                        int l = k;
                        while(path.states[l] != nfa.group[i][j].second && l < path.states.size())
                            l++;
                        if(l >= path.states.size())
                            j--;
                        else
                        {
                            std::string str0;
                            for(int m = k; m < l; m++)
                                str0.append(path.consumes[m]);
                            temp.push_back(str0);
                            break;
                        }
                    }
                }
                if(j < 0)
                {
                    temp.push_back("");
                    continue;
                }
            }
            
            result.push_back(temp);
        }
        else
            nfa.p++;
    }

    return result;
    
    // return {};
}

/**
 * 在给定的输入文本上，进行基于正则表达式的替换，返回替换完成的结果。
 * 需要支持分组替换，如$1表示将此处填入第一个分组匹配到的内容。具体的规则和例子详见文档。
 * @param text 输入的文本
 * @param replacement 要将每一处正则表达式的匹配结果替换为什么内容
 * @return 替换后的文本
 */
std::string Regex::replaceAll(std::string text, std::string replacement) {
    // TODO 请你完成这个函数

    std::vector<std::vector<std::string>> result;

    std::vector<int> match_index;

    int len = text.length();

    nfa.p = 0;
    while(nfa.p < len)
    {
        std::vector<std::string> temp;

        Path path = nfa.exec(text);
        if(!path.states.empty())
        {
            std::string str;
            for(int j = 0; j < path.consumes.size(); j++)
                str.append(path.consumes[j]);
            temp.push_back(str);

            match_index.push_back(nfa.p-str.length());

            for(int i = 0; i < nfa.group_num; i++)
            {
                int j = nfa.group[i].size()-1;
                while(j >= 0)
                {
                    int k = path.states.size()-1;
                    while(path.states[k] != nfa.group[i][j].first && k >= 0)
                        k--;
                    if(k < 0)
                        j--;
                    else
                    {
                        int l = k;
                        while(path.states[l] != nfa.group[i][j].second && l < path.states.size())
                            l++;
                        if(l >= path.states.size())
                            j--;
                        else
                        {
                            std::string str0;
                            for(int m = k; m < l; m++)
                                str0.append(path.consumes[m]);
                            temp.push_back(str0);
                            break;
                        }
                    }
                }
                if(j < 0)
                {
                    temp.push_back("");
                    continue;
                }
            }
            
            result.push_back(temp);
        }
        else
            nfa.p++;
    }
    
    for(int i = match_index.size()-1; i >= 0; i--)
    {
        int j = 0;
        std::string tmp = replacement;
        while(j < tmp.length())
        {
            if(tmp[j] != '$' || (tmp[j] == '$' && j == tmp.length()-1))
            {
                j++;
                continue;
            }
            // if(tmp[j] == '$' && j < tmp.length()-1)
            else
            {
                if(tmp[j+1] == '$')
                {
                    tmp.erase(j, 1);
                    j++;
                    continue;
                }
                else if(tmp[j+1] >= '0' && tmp[j+1] <= '9')
                {
                    int k = j + 1;
                    while(tmp[k] >= '0' && tmp[k] <= '9')
                        k++;
                    int num = std::stoi(tmp.substr(j+1, k-j-1));
                    if(num < result[i].size())
                    {
                        tmp.replace(j, k-j, result[i][num]);
                        j += result[i][num].length();
                        continue;
                    }
                    else
                    {
                        tmp.erase(j, k-j);
                        continue;
                    }
                }
                else
                {
                    j++;
                    continue;
                }

            }
        }
        text.replace(match_index[i], result[i][0].length(), tmp);
    }


    return text;
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
