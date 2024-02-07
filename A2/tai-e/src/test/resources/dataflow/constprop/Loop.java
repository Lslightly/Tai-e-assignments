class Loop {
    void whileUndefinedConstant() {
        int a, b, c;
        int i = 0;
        while (i < 10) {
            a = b;
            b = c;
            c = 1;
            ++i;
        }
    }
}
