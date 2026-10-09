#include <iostream>
#include <cmath>
#include <string>
#include <vector>
#include <cctype>
#include <sstream>
#include <map>
#include <complex>
#include <iomanip>
using namespace std;

// =========全局数学常数=========
const double PI             = acos(-1.0);
const double E              = exp(1.0);
const double GAMMA_EULER    = 0.5772156649015329;
const double CATALAN        = 0.915965594177219;
const double PHI            = (1.0 + sqrt(5.0)) / 2.0;
const double PSI_GOLD       = (1.0 - sqrt(5.0)) / 2.0;
const double A_GLA          = 1.282427129100626;
const double K1OVERSQRT2    = 1.854074677301372;
const double EPS            = 1e-12;

// ==========自定义Complex============
struct Complex
{
    double real;
    double imag;
    Complex(double r = 0, double i = 0) : real(r), imag(i) {}
};
Complex operator+(const Complex& a, const Complex& b){ return {a.real+b.real, a.imag+b.imag}; }
Complex operator-(const Complex& a, const Complex& b){ return {a.real-b.real, a.imag-b.imag}; }
Complex operator*(const Complex& a, const Complex& b)
{
    return {a.real*b.real - a.imag*b.imag, a.real*b.imag + a.imag*b.real};
}
Complex operator/(const Complex& a, const Complex& b)
{
    double den = b.real*b.real + b.imag*b.imag;
    return {(a.real*b.real + a.imag*b.imag)/den, (a.imag*b.real - a.real*b.imag)/den};
}

complex<double> toStd(const Complex& z){ return complex<double>(z.real,z.imag); }
Complex fromStd(const complex<double>& z){ return Complex(z.real(),z.imag()); }

Complex cpow(const Complex& x, const Complex& y)
{
    complex<double> zx=toStd(x), zy=toStd(y);
    return fromStd(pow(zx,zy));
}

Complex c_exp(const Complex& z)  { return fromStd(exp(toStd(z))); }
Complex c_ln(const Complex& z)   { return fromStd(log(toStd(z))); }
Complex c_sqrt(const Complex& z) { return fromStd(sqrt(toStd(z))); }

Complex c_sin(const Complex& z)  { return fromStd(sin(toStd(z))); }
Complex c_cos(const Complex& z)  { return fromStd(cos(toStd(z))); }
Complex c_tan(const Complex& z)  { return fromStd(tan(toStd(z))); }
Complex c_sinh(const Complex& z) { return fromStd(sinh(toStd(z))); }
Complex c_cosh(const Complex& z) { return fromStd(cosh(toStd(z))); }
Complex c_tanh(const Complex& z) { return fromStd(tanh(toStd(z))); }

// ---------------- Lanczos伽马 Γ(z) ----------------
Complex c_gamma(const Complex& z)
{
    const double g=7.0;
    const double coeff[] = {0.99999999999980993,
        676.5203681218851,  -1259.1392167224028,
        771.32342877765313, -176.61502916214059,
        12.507343278686905, -0.13857109526572012,
        9.984369578019571e-6, 1.5056327351493116e-7};
    complex<double> cz = toStd(z);
    if(real(cz) < 0.5)
{
    Complex z_sub = fromStd(1.0 - cz);
    Complex gamma_sub = c_gamma(z_sub);
    complex<double> s = PI / (sin(PI*cz) * toStd(gamma_sub));
    return fromStd(s);
}
    cz -= 1.0;
    complex<double> x = coeff[0];
    for(int i=1;i<9;i++)
        x += coeff[i]/(cz + double(i));
    complex<double> t = cz + g + 0.5;
    complex<double> res = sqrt(2.0*PI) * pow(t, cz+0.5) * exp(-t) * x;
    return fromStd(res);
}

// ========= Akiyama?Tanigawa生成伯努利数 =========
vector<double> bernoulli(int nMax)
{
    vector<vector<double>> mat(nMax+1, vector<double>(nMax+1,0.0));
    for(int m=0;m<=nMax;m++) mat[m][0] = 1.0/(m+1);
    for(int k=1;k<=nMax;k++)
    {
        for(int m=k;m<=nMax;m++)
        {
            mat[m][k] = (m+1 - k)*mat[m-1][k-1];
        }
    }
    vector<double> B(nMax+1);
    for(int k=0;k<=nMax;k++) B[k] = mat[k][k];
    return B;
}

static const int M_TERM    = 9801;
static const int BERNO_ORD = 100;
vector<double> B_even;

Complex f_deriv(const Complex& s, double x, int m)
{
    complex<double> cs=toStd(s);
    complex<double> term(1,0);
    for(int k=0;k<m;k++){
        term *= -(cs + double(k));
    }
    complex<double> xpow = pow(complex<double>(x,0), -cs - double(m));
    return fromStd(term * xpow);
}

Complex int_pow(const Complex& s, double a, double b)
{
    Complex one{1,0};
    Complex sp1 = s + one;
    Complex ba = cpow(Complex{b,0}, sp1);
    Complex aa = cpow(Complex{a,0}, sp1);
    return (ba - aa)/sp1;
}

Complex zeta_euler_maclaurin(const Complex& s)
{
    complex<double> cs=toStd(s);
    Complex sum{0,0};
    for(int n=1;n<M_TERM;n++)
    {
        sum = sum + fromStd(pow(complex<double>(n,0), -cs));
    }
    double M = double(M_TERM);
    Complex fM = fromStd(pow(complex<double>(M,0), -cs));
    Complex f1 = fromStd(pow(complex<double>(1.0,0), -cs));

    Complex integ = int_pow(s,1.0,M);
    Complex total = sum + integ + (f1 + fM)/Complex{2,0};

    for(int k=0;k<BERNO_ORD;k++)
    {
        int idxB = 2*k+2;
        double bval = B_even[idxB];
        int m = 2*k + 1;
        Complex dM = f_deriv(s, M, m);
        Complex d1 = f_deriv(s, 1.0, m);
        double fact = 1.0;
        for(int i=2;i<=2*k+2;i++) fact *= double(i);
        total = total + Complex{bval/fact,0} * (dM - d1);
    }
    return total;
}

Complex c_zeta(const Complex& s)
{
    double re = s.real;
    if(re > 1.0)
    {
        return zeta_euler_maclaurin(s);
    }
    Complex one_minus_s{1.0 - s.real, -s.imag};
    Complex z1s = zeta_euler_maclaurin(one_minus_s);
    Complex g1s = c_gamma(one_minus_s);

    Complex two_pow_s = cpow(Complex{2,0}, s);
    Complex pi_pow_s_1 = cpow(Complex{PI,0}, Complex{s.real-1, s.imag});
    Complex sin_ps2 = c_sin( s * Complex{PI,0} / Complex{2,0} );

    Complex res = two_pow_s * pi_pow_s_1 * sin_ps2 * g1s * z1s;
    return res;
}

void printComplex(const Complex& num)
{
    if(fabs(num.imag) < EPS)
    {
        cout << num.real << endl;
        return;
    }
    if(fabs(num.real) < EPS)
    {
        if(num.imag >= 0) cout << num.imag << "i\n";
        else cout << "-" << -num.imag << "i\n";
        return;
    }
    if(num.imag >= 0)
        cout << num.real << " + " << num.imag << "i" << endl;
    else
        cout << num.real << " - " << -num.imag << "i" << endl;
}

// =========词法记号========
enum TokenType {
    TOK_NUM, TOK_E, TOK_PI, TOK_I, TOK_K,
    TOK_GAMMA_EULER, TOK_CATALAN, TOK_PHI, TOK_PSI_GOLD, TOK_A_GLA, TOK_K1OVERSQRT2,
    TOK_PLUS,TOK_MINUS,TOK_MUL,TOK_DIV,TOK_POW,TOK_POWTOWER,
    TOK_LPAREN,TOK_RPAREN,TOK_COMMA,
    TOK_FUNC_SIN,TOK_FUNC_COS,TOK_FUNC_TAN,
    TOK_FUNC_SINH,TOK_FUNC_COSH,TOK_FUNC_TANH,
    TOK_FUNC_ASIN,TOK_FUNC_ACOS,TOK_FUNC_ATAN,
    TOK_FUNC_EXP,TOK_FUNC_LN,TOK_FUNC_SQRT,
    TOK_FUNC_GAMMA,TOK_FUNC_ZETA,
    TOK_FUNC_SUM,TOK_FUNC_PROD,
    TOK_EOF
};

struct Token {
    TokenType type;
    double numVal;
    Token(TokenType t=TOK_EOF,double v=0):type(t),numVal(v){}
};

vector<Token> tokens;
size_t pos;
map<string,Complex> symEnv;

void tokenize(const string &s)
{
    tokens.clear(); pos=0;
    size_t i=0,n=s.size();
    while(i<n)
    {
        char ch=s[i];
        if(isspace(ch)){i++;continue;}
        if(isdigit(ch)||ch=='.')
        {
            size_t j=i;
            while(j<n&&(isdigit(s[j])||s[j]=='.'||((s[j]=='e'||s[j]=='E')&&(j+1<n&&(isdigit(s[j+1])||s[j+1]=='+'||s[j+1]=='-'))))) j++;
            double v=stod(s.substr(i,j-i));
            tokens.emplace_back(TOK_NUM,v);
            i=j;
        }
        else if(s.substr(i,2)=="#e")          {tokens.emplace_back(TOK_E);i+=2;}
        else if(s.substr(i,3)=="#pi")         {tokens.emplace_back(TOK_PI);i+=3;}
        else if(s.substr(i,11)=="#gamma_euler"){tokens.emplace_back(TOK_GAMMA_EULER);i+=11;}
        else if(s.substr(i,9)=="#catalan")     {tokens.emplace_back(TOK_CATALAN);i+=9;}
        else if(s.substr(i,5)=="#phi")         {tokens.emplace_back(TOK_PHI);i+=5;}
        else if(s.substr(i,9)=="#psi_gold")    {tokens.emplace_back(TOK_PSI_GOLD);i+=9;}
        else if(s.substr(i,6)=="#A_gla")       {tokens.emplace_back(TOK_A_GLA);i+=6;}
        else if(s.substr(i,13)=="#K1overSqrt2"){tokens.emplace_back(TOK_K1OVERSQRT2);i+=13;}
        else if(s[i]=='i'){tokens.emplace_back(TOK_I);i++;}
        else if(s[i]=='k'){tokens.emplace_back(TOK_K);i++;}
        else if(s.substr(i,2)=="^^"){tokens.emplace_back(TOK_POWTOWER);i+=2;}
        else if(ch=='^'){tokens.emplace_back(TOK_POW);i++;}
        else if(ch=='+'){tokens.emplace_back(TOK_PLUS);i++;}
        else if(ch=='-'){tokens.emplace_back(TOK_MINUS);i++;}
        else if(ch=='*'){tokens.emplace_back(TOK_MUL);i++;}
        else if(ch=='/'){tokens.emplace_back(TOK_DIV);i++;}
        else if(ch=='('){tokens.emplace_back(TOK_LPAREN);i++;}
        else if(ch==')'){tokens.emplace_back(TOK_RPAREN);i++;}
        else if(ch==','){tokens.emplace_back(TOK_COMMA);i++;}
        else if(s.substr(i,3)=="sin"){tokens.emplace_back(TOK_FUNC_SIN);i+=3;}
        else if(s.substr(i,3)=="cos"){tokens.emplace_back(TOK_FUNC_COS);i+=3;}
        else if(s.substr(i,3)=="tan"){tokens.emplace_back(TOK_FUNC_TAN);i+=3;}
        else if(s.substr(i,4)=="sinh"){tokens.emplace_back(TOK_FUNC_SINH);i+=4;}
        else if(s.substr(i,4)=="cosh"){tokens.emplace_back(TOK_FUNC_COSH);i+=4;}
        else if(s.substr(i,4)=="tanh"){tokens.emplace_back(TOK_FUNC_TANH);i+=4;}
        else if(s.substr(i,4)=="asin"){tokens.emplace_back(TOK_FUNC_ASIN);i+=4;}
        else if(s.substr(i,4)=="acos"){tokens.emplace_back(TOK_FUNC_ACOS);i+=4;}
        else if(s.substr(i,4)=="atan"){tokens.emplace_back(TOK_FUNC_ATAN);i+=4;}
        else if(s.substr(i,3)=="exp"){tokens.emplace_back(TOK_FUNC_EXP);i+=3;}
        else if(s.substr(i,2)=="ln"){tokens.emplace_back(TOK_FUNC_LN);i+=2;}
        else if(s.substr(i,4)=="sqrt"){tokens.emplace_back(TOK_FUNC_SQRT);i+=4;}
        else if(s.substr(i,5)=="gamma"){tokens.emplace_back(TOK_FUNC_GAMMA);i+=5;}
        else if(s.substr(i,4)=="zeta"){tokens.emplace_back(TOK_FUNC_ZETA);i+=4;}
        else if(s.substr(i,3)=="sum"){tokens.emplace_back(TOK_FUNC_SUM);i+=3;}
        else if(s.substr(i,4)=="prod"){tokens.emplace_back(TOK_FUNC_PROD);i+=4;}
        else { i++; }
    }
    tokens.emplace_back(TOK_EOF);
}

Token peek(){ return tokens[pos]; }
void consume(){ pos++; }

Complex parseExpr();
Complex parsePowTower();
Complex parsePow();
Complex parseMulDiv();
Complex parseAddSub();
Complex parsePrimary();

Complex parseExpr(){ return parseAddSub(); }
Complex parseAddSub()
{
    Complex val=parseMulDiv();
    while(peek().type==TOK_PLUS||peek().type==TOK_MINUS)
    {
        Token op=peek(); consume();
        Complex r=parseMulDiv();
        if(op.type==TOK_PLUS) val = val + r;
        else val = val - r;
    }
    return val;
}
Complex parseMulDiv()
{
    Complex val=parsePowTower();
    while(peek().type==TOK_MUL||peek().type==TOK_DIV)
    {
        Token op=peek(); consume();
        Complex r=parsePowTower();
        if(op.type==TOK_MUL) val = val * r;
        else val = val / r;
    }
    return val;
}
Complex parsePowTower()
{
    vector<Complex> st;
    st.push_back(parsePow());
    while(peek().type==TOK_POWTOWER)
    {
        consume();
        st.push_back(parsePow());
    }
    if(st.size()==1) return st[0];
    Complex res=st.back();
    for(int i=(int)st.size()-2;i>=0;i--)
    {
        res = cpow(st[i], res);
    }
    return res;
}
Complex parsePow()
{
    Complex val=parsePrimary();
    while(peek().type==TOK_POW)
    {
        consume();
        Complex r=parsePrimary();
        val = cpow(val, r);
    }
    return val;
}
Complex parsePrimary()
{
    Token t=peek();
    if(t.type==TOK_MINUS)
    {
        consume();
        Complex sub=parsePrimary();
        return Complex{-sub.real, -sub.imag};
    }
    if(t.type==TOK_NUM)          { consume(); return {t.numVal,0}; }
    if(t.type==TOK_E)            { consume(); return {E,0}; }
    if(t.type==TOK_PI)           { consume(); return {PI,0}; }
    if(t.type==TOK_GAMMA_EULER)  { consume(); return {GAMMA_EULER,0}; }
    if(t.type==TOK_CATALAN)      { consume(); return {CATALAN,0}; }
    if(t.type==TOK_PHI)          { consume(); return {PHI,0}; }
    if(t.type==TOK_PSI_GOLD)     { consume(); return {PSI_GOLD,0}; }
    if(t.type==TOK_A_GLA)        { consume(); return {A_GLA,0}; }
    if(t.type==TOK_K1OVERSQRT2)  { consume(); return {K1OVERSQRT2,0}; }
    if(t.type==TOK_I)            { consume(); return {0,1}; }
    if(t.type==TOK_K)            { consume(); return symEnv["k"]; }

    if(t.type==TOK_LPAREN)
    {
        consume();
        Complex v=parseExpr();
        if(peek().type==TOK_RPAREN) consume();
        return v;
    }

    TokenType ft=t.type; consume();
    if(peek().type!=TOK_LPAREN) return {0,0};
    consume();

    if(ft==TOK_FUNC_SIN)   { Complex a=parseExpr(); consume(); return c_sin(a); }
    if(ft==TOK_FUNC_COS)   { Complex a=parseExpr(); consume(); return c_cos(a); }
    if(ft==TOK_FUNC_TAN)   { Complex a=parseExpr(); consume(); return c_tan(a); }
    if(ft==TOK_FUNC_SINH)  { Complex a=parseExpr(); consume(); return c_sinh(a); }
    if(ft==TOK_FUNC_COSH)  { Complex a=parseExpr(); consume(); return c_cosh(a); }
    if(ft==TOK_FUNC_TANH)  { Complex a=parseExpr(); consume(); return c_tanh(a); }
    if(ft==TOK_FUNC_ASIN)  { Complex a=parseExpr(); consume(); return fromStd(asin(toStd(a))); }
    if(ft==TOK_FUNC_ACOS)  { Complex a=parseExpr(); consume(); return fromStd(acos(toStd(a))); }
    if(ft==TOK_FUNC_ATAN)  { Complex a=parseExpr(); consume(); return fromStd(atan(toStd(a))); }
    if(ft==TOK_FUNC_EXP)   { Complex a=parseExpr(); consume(); return c_exp(a); }
    if(ft==TOK_FUNC_LN)    { Complex a=parseExpr(); consume(); return c_ln(a); }
    if(ft==TOK_FUNC_SQRT)  { Complex a=parseExpr(); consume(); return c_sqrt(a); }
    if(ft==TOK_FUNC_GAMMA) { Complex a=parseExpr(); consume(); return c_gamma(a); }
    if(ft==TOK_FUNC_ZETA)  { Complex a=parseExpr(); consume(); return c_zeta(a); }

    if(ft==TOK_FUNC_SUM)
    {
        Complex start=parseExpr(); consume();
        Complex end=parseExpr(); consume();
        Complex sum{0,0};
        double s=start.real, e=end.real;
        for(double k=s;k<=e+EPS;k+=1.0)
        {
            symEnv["k"] = {k,0};
            Complex term = parseExpr();
            sum = sum + term;
        }
        consume();
        symEnv.erase("k");
        return sum;
    }
    if(ft==TOK_FUNC_PROD)
    {
        Complex start=parseExpr(); consume();
        Complex end=parseExpr(); consume();
        Complex prod{1,0};
        double s=start.real, e=end.real;
        for(double k=s;k<=e+EPS;k+=1.0)
        {
            symEnv["k"] = {k,0};
            Complex term = parseExpr();
            prod = prod * term;
        }
        consume();
        symEnv.erase("k");
        return prod;
    }
    return {0,0};
}

Complex evalComplex(const string &expr)
{
    tokenize(expr);
    pos=0;
    symEnv.clear();
    return parseExpr();
}

// ======================【菜单向导函数】======================
// 读取一个复数
Complex promptReadComplex(const char* tip)
{
    double r,i;
    cout << tip;
    cin >> r >> i;
    return Complex(r,i);
}

// 二元运算向导：a op b
void wizardBinary(const char* opName, Complex(*op)(const Complex&,const Complex&))
{
    cout << "\n===== " << opName << " =====\n";
    Complex a = promptReadComplex("输入第一个复数（实部 虚部）：");
    Complex b = promptReadComplex("输入第二个复数（实部 虚部）：");
    Complex res = op(a,b);
    cout << opName << " 结果：";
    printComplex(res);
    cout << "============================\n";
    cin.ignore();
}

// 一元函数向导 f(z)
void wizardUnary(const char* funcName, Complex(*f)(const Complex&))
{
    cout << "\n===== " << funcName << " =====\n";
    Complex z = promptReadComplex("输入复数参数（实部 虚部）：");
    Complex res = f(z);
    cout << funcName << " 结果：";
    printComplex(res);
    cout << "============================\n";
    cin.ignore();
}

// 复数幂向导 x^y
void wizardCpow()
{
    cout << "\n=====复数幂 x^y=====\n";
    Complex x = promptReadComplex("输入底数x（实部 虚部）：");
    Complex y = promptReadComplex("输入指数y（实部 虚部）：");
    Complex res = cpow(x,y);
    cout << "x^y 结果：";
    printComplex(res);
    cout << "============================\n";
    cin.ignore();
}

// sum求和向导【支持自定义步长step】
void wizardSum()
{
    cout << "\n=====级数 sum(start,end,step,expr)=====\n";
    double start,end,step;
    string exprStr;
    cout << "输入循环起始值(实数)：";
    cin >> start;
    cout << "输入循环终止值(实数)：";
    cin >> end;
    cout << "输入循环步长(实数，正数/负数，禁止0)：";
    cin >> step;
    cin.ignore();

    if(fabs(step) < EPS)
    {
        cout << "错误：步长不能为0，直接退出求和！\n";
        return;
    }

    cout << "输入表达式(可用循环变量k，例：k、k^2)：";
    getline(cin,exprStr);

    Complex sum{0,0};
    double k = start;
    // 正向、反向循环判断
    while( (step>0 && k <= end+EPS) || (step<0 && k >= end-EPS) )
    {
        symEnv["k"] = Complex(k,0);
        Complex term = evalComplex(exprStr);
        sum = sum + term;
        k += step;
    }
    symEnv.erase("k");
    cout << "sum 结果：";
    printComplex(sum);
    cout << "========================================\n";
}

// prod连乘向导【支持自定义步长step】
void wizardProd()
{
    cout << "\n=====连乘 prod(start,end,step,expr)=====\n";
    double start,end,step;
    string exprStr;
    cout << "输入循环起始值(实数)：";
    cin >> start;
    cout << "输入循环终止值(实数)：";
    cin >> end;
    cout << "输入循环步长(实数，正数/负数，禁止0)：";
    cin >> step;
    cin.ignore();

    if(fabs(step) < EPS)
    {
        cout << "错误：步长不能为0，直接退出连乘！\n";
        return;
    }

    cout << "输入表达式(可用循环变量k，例：k、k+1)：";
    getline(cin,exprStr);

    Complex prod{1,0};
    double k = start;
    while( (step>0 && k <= end+EPS) || (step<0 && k >= end-EPS) )
    {
        symEnv["k"] = Complex(k,0);
        Complex term = evalComplex(exprStr);
        prod = prod * term;
        k += step;
    }
    symEnv.erase("k");
    cout << "prod 结果：";
    printComplex(prod);
    cout << "=========================================\n";
}

// 主菜单
void showMenu()
{
    cout << "\n==========运算选择菜单==========\n";
    cout << "【二元运算】\n";
    cout << " 1 : 复数加法  a + b\n";
    cout << " 2 : 复数减法  a - b\n";
    cout << " 3 : 复数乘法  a * b\n";
    cout << " 4 : 复数除法  a / b\n";
    cout << " 5 : 复数幂    x ^ y\n";
    cout << "【一元函数】\n";
    cout << " 6 : gamma(z) 伽马函数\n";
    cout << " 7 : zeta(s)  黎曼ζ函数\n";
    cout << " 8 : sqrt(z)  平方根\n";
    cout << " 9 : exp(z)   指数函数\n";
    cout << "10 : ln(z)    自然对数\n";
    cout << "11 : sin(z)   正弦\n";
    cout << "12 : cos(z)   余弦\n";
    cout << "13 : tan(z)   正切\n";
    cout << "14 : sinh(z)  双曲正弦\n";
    cout << "15 : cosh(z)  双曲余弦\n";
    cout << "16 : tanh(z)  双曲正切\n";
    cout << "【级数/连乘（支持自定义步长）】\n";
    cout << "17 : sum(start,end,step,expr) 级数求和\n";
    cout << "18 : prod(start,end,step,expr) 连乘\n";
    cout << "【其他命令】\n";
    cout << " 0 : 返回主交互提示符\n";
    cout << "================================\n";
    cout << "请输入选择编号：";
}

void menuWizard()
{
    int sel;
    while(true)
    {
        showMenu();
        cin >> sel;
        cin.ignore();
        if(sel == 0)
        {
            cout << "退出运算选择菜单\n";
            break;
        }
        switch(sel)
        {
            case 1: wizardBinary("复数加法", operator+); break;
            case 2: wizardBinary("复数减法", operator-); break;
            case 3: wizardBinary("复数乘法", operator*); break;
            case 4: wizardBinary("复数除法", operator/); break;
            case 5: wizardCpow(); break;
            case 6: wizardUnary("gamma(z)", c_gamma); break;
            case 7: wizardUnary("zeta(s)", c_zeta); break;
            case 8: wizardUnary("sqrt(z)", c_sqrt); break;
            case 9: wizardUnary("exp(z)", c_exp); break;
            case10: wizardUnary("ln(z)", c_ln); break;
            case11: wizardUnary("sin(z)", c_sin); break;
            case12: wizardUnary("cos(z)", c_cos); break;
            case13: wizardUnary("tan(z)", c_tan); break;
            case14: wizardUnary("sinh(z)", c_sinh); break;
            case15: wizardUnary("cosh(z)", c_cosh); break;
            case16: wizardUnary("tanh(z)", c_tanh); break;
            case17: wizardSum(); break;
            case18: wizardProd(); break;
            default: cout<<"无效编号，请重新选择\n";
        }
    }
}

// 表达式向导
void calcWizard()
{
    cout << "\n--------【表达式引导输入模式】--------" << endl;
    cout << "直接输入完整数学表达式；输入 back 返回\n";
    cout << "------------------------------------------\n";
    string line;
    while(true)
    {
        cout << "[calc]> ";
        getline(cin,line);
        if(line=="back"){
            cout << "退出表达式模式\n";
            return;
        }
        Complex r=evalComplex(line);
        printComplex(r);
    }
}

void printHelpInfo()
{
    cout << "\n========复数特殊函数计算器 帮助========" << endl;
    cout << "【参数】M_TERM="<<M_TERM<<" , BERNO_ORD="<<BERNO_ORD<<endl;
    cout << "【警告】zeta(s)计算开销大\n";
    cout << "\n命令：\n";
    cout << " menu    打开分步运算选择菜单\n";
    cout << " calc    表达式输入模式\n";
    cout << " help    打印本帮助\n";
    cout << " quit    退出程序\n";
    cout << "\n常数：#e #pi #gamma_euler #phi #psi_gold #catalan #A_gla #K1overSqrt2 , i\n";
    cout << "运算符:+ - * / ^ ^^ ;函数:sin,cos,tan,sinh,cosh,tanh,exp,ln,sqrt,gamma,zeta,sum,prod\n";
    cout << "---------------------------------------------\n";
}

int main()
{
    cout << "========复数特殊函数计算器========" << endl;
    cout << "正在预生成伯努利数 B0…B"<<2*BERNO_ORD<<" …\n";
    B_even = bernoulli(2*BERNO_ORD);
    cout << "伯努利数生成完成。\n";
    printHelpInfo();

    string line;
    while(true)
    {
        cout << "> ";
        getline(cin,line);
        if(line=="quit") break;
        if(line=="help"){ printHelpInfo(); continue; }
        if(line=="menu"){ menuWizard(); continue; }
        if(line=="calc"){ calcWizard(); continue; }
        if(line.substr(0,4)=="pow:")
        {
            size_t c=line.find(',');
            string sx=line.substr(4,c-4);
            string sy=line.substr(c+1);
            Complex x=evalComplex(sx);
            Complex y=evalComplex(sy);
            Complex res=cpow(x,y);
            printComplex(res);
        }
        else
        {
            Complex r=evalComplex(line);
            printComplex(r);
        }
    }
    cout<<"程序结束\n";
    return 0;
}

