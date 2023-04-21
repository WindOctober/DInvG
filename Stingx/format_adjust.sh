#!/bin/bash

# 指定要搜索的文件夹，用 . 表示当前文件夹
FOLDER="."

# 使用 find 命令查找 .cc, .l, .y 后缀的文件，并将它们传递给 clang-format
find "$FOLDER" \( -iname "*.cc" -o -iname "*.h" \) -type f -exec clang-format -i {} \;

# 打印完成消息
echo "所有 .cc, .h 文件已使用 clang-format 进行格式化。"
