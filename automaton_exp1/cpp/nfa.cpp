#include "nfa.h"
#include <sstream>

/**
 * 判断当前规则是否与输入的字符匹配，这里不包括epsilon转移的情况
 * @param a 字符
 * @return 若匹配则返回true，否则返回false
*/
bool Rule::match(char a)
{
    if(type == NORMAL)
        return (a == by[0]);
    else if(type == RANGE)
        return (a >= by[0] && a <= to[0]);
    else if(type == SPECIAL)
    {
        if(by == ".")
            return (a != '\n' && a != '\r');
        else if(by == "d")
            return (a >= '0' && a <= '9');
        else if(by == "s")
            return (a == '\f' || a == '\n' || a == '\r' || a == '\t' || a == '\v');
        else if(by == "w")
            return (a == '_' || (a >= 'a' && a <= 'z') || (a >= 'A' && a <= 'Z') || (a >= '0' && a <= '9'));
        else if(by == "D")
            return !(a >= '0' && a <= '9');
        else if(by == "S")
            return !(a == '\f' || a == '\n' || a == '\r' || a == '\t' || a == '\v');
        else
        // else if(by == "F")
            return !(a == '_' || (a >= 'a' && a <= 'z') || (a >= 'A' && a <= 'Z') || (a >= '0' && a <= '9'));
    }
    else 
        return true;
}

/**
 * 回溯路径
 * @param path 记录了每一步的状态和剩余的字符串
 * @return 返回一个Path
*/
Path NFA::backtrace(path_element path[])
{
    Path temp;
    int size = 0;
    while(path[size].q != -1)
        size++;
    for(int i = 0; i < size; i++)
    {
        temp.states.push_back(path[i].q);
        if(i < size-1)
        {
            if(path[i].str == path[i+1].str)
                temp.consumes.push_back("");
            else
                temp.consumes.push_back(path[i].str.substr(0, 1));
        }
    }
    return temp;
}

/**
 * 在自动机上执行指定的输入字符串。
 * @param text 输入字符串
 * @return 若拒绝，请 return Path::reject(); 。若接受，请手工构造一个Path的实例并返回。
 */
Path NFA::exec(std::string text) {
    // TODO 请你完成这个函数

    std::vector<stack_element> Stack;

    std::set<std::string> Set[10003]; //使用集合存储在该状态时曾经有过的字符串，用于排除epsilon转移时可能出现的死循环

    Stack.push_back({0, text, 0});
    Set[0].insert(text);

    path_element path[10003];

    while(!Stack.empty())
    {
        stack_element temp = Stack.back();
        Stack.pop_back();

        path[temp.step].q = temp.q;
        path[temp.step].str = temp.str;

        if(is_final[temp.q] && temp.str.empty())
            return backtrace(path);
        
        for(Rule i : rules[temp.q])
        {
            if(i.type == EPSILON)
            {
                //如果是epsilon转移，需要判断之前是否出现重复的状态，即，状态以及剩余字符相同，防止死循环
                if(Set[i.dst].count(temp.str))
                    continue;
                
                stack_element temp2;
                temp2.q = i.dst;
                temp2.str = temp.str;
                temp2.step = temp.step + 1;

                Stack.push_back(temp2);
                Set[temp2.q].insert(temp.str);
            }
            else if(i.match(temp.str[0]) && !temp.str.empty())
            {
                stack_element temp2;
                temp2.q = i.dst;
                temp2.str = temp.str.substr(1);
                temp2.step = temp.step + 1;

                Stack.push_back(temp2);
                Set[temp2.q].insert(temp2.str);
            }
        }
    }

    return Path::reject();
}

/**
 * 将Path转为（序列化为）文本的表达格式（以便于通过stdout输出）
 * 你不需要理解此函数的含义、阅读此函数的实现和调用此函数。
 */
std::ostream &operator<<(std::ostream &os, Path &path) {
    if (!path.states.empty()) {
        if (path.consumes.size() != path.states.size() - 1)
            throw std::runtime_error("Path的len(consumes)不等于len(states)-1！");
        for (int i = 0; i < path.consumes.size(); ++i) {
            os << path.states[i] << " " << path.consumes[i] << " ";
        }
        os << path.states[path.states.size() - 1];
    } else os << std::string("Reject");
    return os;
}

/**
 * 从自动机的文本表示构造自动机
 * 你不需要理解此函数的含义、阅读此函数的实现和调用此函数。
 */
NFA NFA::from_text(const std::string &text) {
    NFA nfa = NFA();
    bool reading_rules = false;
    std::istringstream ss(text);
    std::string line;
    while (std::getline(ss, line)) {
        if (line.empty()) continue;
        if (line.find("states:") == 0) {
            nfa.num_states = std::stoi(line.substr(7));
            for (int i = 0; i < nfa.num_states; ++i) {
                nfa.rules.emplace_back();
                nfa.is_final.push_back(false);
            }
            continue;
        } else if (line.find("final:") == 0) {
            if (nfa.num_states == 0) throw std::runtime_error("states必须出现在final和rules之前!");
            std::istringstream ss2(line.substr(6));
            int t;
            while (true) {
                ss2 >> t;
                if (!ss2.fail()) nfa.is_final[t] = true;
                else break;
            }
            reading_rules = false;
            if (ss2.eof()) continue;
        } else if (line.find("rules:") == 0) {
            if (nfa.num_states == 0) throw std::runtime_error("states必须出现在final和rules之前!");
            reading_rules = true;
            continue;
        } else if (line.find("input:") == 0) {
            reading_rules = false;
            continue;
        } else if (reading_rules) {
            auto arrow_pos = line.find("->"), space_pos = line.find(' ');
            if (arrow_pos != std::string::npos && space_pos != std::string::npos && arrow_pos < space_pos) {
                int src = std::stoi(line.substr(0, arrow_pos));
                int dst = std::stoi(line.substr(arrow_pos + 2, space_pos - (arrow_pos + 2)));
                auto content = line.substr(space_pos + 1);
                bool success = true;
                while (success && !content.empty()) {
                    auto p = content.find(' ');
                    if (p == std::string::npos) p = content.size();
                    else if (p == 0) p = 1; // 当第一个字母是空格时，说明转移的字符就是空格。于是假定第二个字母也是空格（如果不是，会在后面直接报错）
                    Rule rule{dst};
                    if (p == 3 && content[1] == '-') {
                        rule.type = RANGE;
                        rule.by = content[0];
                        rule.to = content[2];
                    } else if (p == 2 && content[0] == '\\') {
                        if (content[1] == 'e') rule.type = EPSILON;
                        else {
                            rule.type = SPECIAL;
                            rule.by = content[1];
                        }
                    } else if (p == 1 && (p >= content.length() || content[p] == ' ')) {
                        rule.type = NORMAL;
                        rule.by = content[0];
                    } else success = false;
                    nfa.rules[src].push_back(rule);
                    content = content.substr(std::min(p + 1, content.size()));
                }
                if (success) continue;
            }
        }
        throw std::runtime_error("无法parse输入文件！失败的行： " + line);
    }
    if (!ss.eof()) throw std::runtime_error("无法parse输入文件！(stringstream在getline的过程中发生错误)");;
    return nfa;
}
