操作系统：Windows10
架构：VSCode
编译器：mingw g++8.1.0

参考了课件上所讲的思路，使用回溯法，基于DFS，使用栈存储。实际代码中直接用vector来代替。
然而课件里的伪代码本身有些错误，所以根据需要进行了修改。比如栈push的不应该是input，而是str或者是str[1:]。
关于epsilon死循环的排除，使用了set来存储某个状态时曾经有过的字符串，因为set中的元素互异，如果找到重复了，则直接跳过。