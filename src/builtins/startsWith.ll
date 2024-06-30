define i1 @$builtins$starts_with({i8*, i64} %hay, {i8*, i64} %needle) {
start:
    %hay.ptr = extractvalue {i8*, i64} %hay, 0
    %hay.len = extractvalue {i8*, i64} %hay, 1
    %needle.ptr = extractvalue {i8*, i64} %needle, 0
    %needle.len = extractvalue {i8*, i64} %needle, 1
    %lt = icmp ult i64 %hay.len, %needle.len
    br i1 %lt, label %bb.false, label %loop.header

bb.false:
    ret i1 false

bb.true:
    ret i1 true

loop.header:
    %index = phi i64 [0, %start], [%next_index, %loop.samebyte]
    %lt.2 = icmp ult i64 %index, %needle.len
    br i1 %lt.2, label %loop.body, label %bb.true

loop.body:
    %hayelementptr = getelementptr i8, i8* %hay.ptr, i64 %index
    %needleelementptr = getelementptr i8, i8* %needle.ptr, i64 %index

    %hayelement = load i8, i8* %hayelementptr
    %needleelement = load i8, i8* %needleelementptr

    %samebyte = icmp eq i8 %hayelement, %needleelement
    br i1 %samebyte, label %loop.samebyte, label %bb.false

loop.samebyte:
    %next_index = add i64 %index, 1
    br label %loop.header
}
