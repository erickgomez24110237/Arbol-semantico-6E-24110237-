// ============================================================================
//  Arbol Semantico (Tableau) - Logica Proposicional
//  C++17 + SFML 2.5/2.6  (MinGW-w64, Visual Studio Code)
//
//  Flujo:  texto en espanol -> proposiciones simples (p, q, r...) -> formulas
//          -> tableau (se asume que TODAS las reglas son verdaderas)
//          -> ramas abiertas (modelos) / ramas cerradas (X)
//
//  Compilar:
//   g++ main.cpp -o arbol.exe -std=c++17 -I<SFML>/include -L<SFML>/lib \
//       -lsfml-graphics -lsfml-window -lsfml-system
// ============================================================================
#include <SFML/Graphics.hpp>
#include <algorithm>
#include <cctype>
#include <iostream>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using std::string;
using std::vector;
using std::shared_ptr;

// ----------------------------------------------------------------------------
//  Fuentes y simbolos
// ----------------------------------------------------------------------------
static sf::Font gFontText;   // texto normal (Arial / Segoe UI ...)
static sf::Font gFontSym;    // fuente con simbolos logicos (Segoe UI Symbol)
static bool     gUni = false; // true si podemos dibujar ∧ ∨ ¬ → ↔ ✓ ✕

static sf::String U(const string& s) { return sf::String::fromUtf8(s.begin(), s.end()); }

static bool loadFirst(sf::Font& f, const vector<string>& paths) {
    for (const auto& p : paths)
        if (f.loadFromFile(p)) return true;
    return false;
}

static bool loadFonts() {
    if (!loadFirst(gFontText, {"arial.ttf", "C:/Windows/Fonts/arial.ttf",
                               "C:/Windows/Fonts/segoeui.ttf", "C:/Windows/Fonts/calibri.ttf",
                               "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf"}))
        return false;
    gUni = loadFirst(gFontSym, {"C:/Windows/Fonts/seguisym.ttf",
                                "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf"});
    if (!gUni) gFontSym = gFontText;  // sin simbolos Unicode: usamos ASCII (& | ~ -> <->)
    return true;
}

static const char* symNot()  { return gUni ? "\u00AC" : "~"; }
static const char* symAnd()  { return gUni ? "\u2227" : "&"; }
static const char* symOr()   { return gUni ? "\u2228" : "|"; }
static const char* symImp()  { return gUni ? "\u2192" : "->"; }
static const char* symIff()  { return gUni ? "\u2194" : "<->"; }
static const char* symOk()   { return gUni ? "\u2713" : "(ok)"; }
static const char* symX()    { return gUni ? "\u2715" : "X"; }

// ----------------------------------------------------------------------------
//  Formulas
// ----------------------------------------------------------------------------
struct Formula;
using FP = shared_ptr<Formula>;

struct Formula {
    enum Type { ATOM, NOT, AND, OR, IMPLIES, IFF } type = ATOM;
    string atom;
    FP left, right;

    static FP Atom(const string& a) {
        auto f = std::make_shared<Formula>();
        f->type = ATOM;
        f->atom = a;
        return f;
    }
    static FP Not(const FP& x) {
        auto f = std::make_shared<Formula>();
        f->type = NOT;
        f->left = x;
        return f;
    }
    static FP Bin(Type t, const FP& l, const FP& r) {
        auto f = std::make_shared<Formula>();
        f->type = t;
        f->left = l;
        f->right = r;
        return f;
    }

    // Parentesis solo cuando hacen falta (subformulas binarias dentro de otra)
    string str(bool top = true) const {
        switch (type) {
            case ATOM: return atom;
            case NOT:  return string(symNot()) + left->str(false);
            default: {
                const char* op = type == AND ? symAnd() : type == OR ? symOr()
                               : type == IMPLIES ? symImp() : symIff();
                string s = left->str(false) + " " + op + " " + right->str(false);
                return top ? s : "(" + s + ")";
            }
        }
    }
};

// Clave de literal: "p" o "~p". Devuelve false si no es literal.
static bool literalKey(const FP& f, string& key) {
    if (f->type == Formula::ATOM) { key = f->atom; return true; }
    if (f->type == Formula::NOT && f->left->type == Formula::ATOM) {
        key = "~" + f->left->atom;
        return true;
    }
    return false;
}

// ----------------------------------------------------------------------------
//  Tabla de atomos: misma frase = mismo atomo
// ----------------------------------------------------------------------------
struct AtomTable {
    std::map<string, string> letterOf;                 // frase normalizada -> letra
    vector<std::pair<string, string>> order;           // (letra, frase) en orden de aparicion

    string get(const string& phrase) {
        auto it = letterOf.find(phrase);
        if (it != letterOf.end()) return it->second;
        static const string letters = "pqrstuvwxzabcdefghjklmno";
        size_t n = order.size();
        string l = n < letters.size() ? string(1, letters[n])
                                      : "p" + std::to_string(n - letters.size() + 1);
        letterOf[phrase] = l;
        order.push_back({l, phrase});
        return l;
    }
};

// ----------------------------------------------------------------------------
//  Analizador de lenguaje natural (espanol)
//  Precedencia (de menor a mayor):  <->  <  ->  <  o  <  y  <  no
// ----------------------------------------------------------------------------
static vector<string> normalizeWords(const string& s) {
    string o;
    for (unsigned char c : s) {
        if (c >= 128) continue;  // la entrada ya viene sin acentos
        char ch = static_cast<char>(std::tolower(c));
        if (ch == ',' || ch == '.' || ch == ';' || ch == ':' || ch == '?' || ch == '!') ch = ' ';
        if (ch == '(' || ch == ')') { o += ' '; o += ch; o += ' '; }
        else o += ch;
    }
    vector<string> w;
    std::istringstream is(o);
    string x;
    while (is >> x) w.push_back(x);
    return w;
}

static vector<string> tokenize(const vector<string>& w) {
    vector<string> t;
    auto at = [&](size_t k, const char* s) { return k < w.size() && w[k] == s; };
    size_t i = 0;
    while (i < w.size()) {
        if (at(i, "si") && at(i + 1, "y") && at(i + 2, "solo") && at(i + 3, "si")) { t.push_back("#IFF"); i += 4; }
        else if (at(i, "si") && at(i + 1, "solo") && at(i + 2, "si"))              { t.push_back("#IFF"); i += 3; }
        else if (at(i, "solo") && at(i + 1, "si"))                                  { t.push_back("#IMP"); i += 2; }
        else if (w[i] == "sii" || w[i] == "<->" || w[i] == "<=>")                   { t.push_back("#IFF"); i++; }
        else if (w[i] == "->" || w[i] == "=>" || w[i] == "implica")                 { t.push_back("#IMP"); i++; }
        else if (w[i] == "si")       { t.push_back("#IF");   i++; }
        else if (w[i] == "entonces") { t.push_back("#THEN"); i++; }
        else if (w[i] == "y")        { t.push_back("#AND");  i++; }
        else if (w[i] == "o")        { t.push_back("#OR");   i++; }
        else if (w[i] == "no")       { t.push_back("#NOT");  i++; }
        else                         { t.push_back(w[i]);    i++; }
    }
    return t;
}

static string tokDisplay(const string& t) {
    if (t == "#IF") return "si";
    if (t == "#THEN") return "entonces";
    if (t == "#AND") return "y";
    if (t == "#OR") return "o";
    if (t == "#NOT") return "no";
    if (t == "#IFF") return "si y solo si";
    if (t == "#IMP") return "->";
    return t;
}

struct Parser {
    vector<string> t;
    size_t pos = 0;
    AtomTable& at;

    Parser(vector<string> toks, AtomTable& a) : t(std::move(toks)), at(a) {}

    bool is(const char* s) const { return pos < t.size() && t[pos] == s; }
    string here() const { return pos < t.size() ? "\"" + tokDisplay(t[pos]) + "\"" : "el final de la regla"; }

    FP parseIff() {
        FP l = parseImp();
        while (is("#IFF")) {
            pos++;
            FP r = parseImp();
            l = Formula::Bin(Formula::IFF, l, r);
        }
        return l;
    }
    FP parseImp() {
        if (is("#IF")) {  // si A entonces B
            pos++;
            FP a = parseOr();
            if (!(is("#THEN") || is("#IMP")))
                throw std::runtime_error("Falta \"entonces\" despues de \"si\" (cerca de " + here() + ").");
            pos++;
            FP c = parseImp();
            return Formula::Bin(Formula::IMPLIES, a, c);
        }
        FP l = parseOr();
        if (is("#THEN") || is("#IMP")) {  // A solo si B, A -> B
            pos++;
            FP r = parseImp();
            return Formula::Bin(Formula::IMPLIES, l, r);
        }
        return l;
    }
    FP parseOr() {
        FP l = parseAnd();
        while (is("#OR")) { pos++; FP r = parseAnd(); l = Formula::Bin(Formula::OR, l, r); }
        return l;
    }
    FP parseAnd() {
        FP l = parseNot();
        while (is("#AND")) { pos++; FP r = parseNot(); l = Formula::Bin(Formula::AND, l, r); }
        return l;
    }
    FP parseNot() {
        if (is("#NOT")) { pos++; return Formula::Not(parseNot()); }
        return parsePrimary();
    }
    FP parsePrimary() {
        if (is("(")) {
            pos++;
            FP f = parseIff();
            if (!is(")")) throw std::runtime_error("Falta cerrar un parentesis.");
            pos++;
            return f;
        }
        string words;
        while (pos < t.size() && t[pos][0] != '#' && t[pos] != "(" && t[pos] != ")") {
            if (!words.empty()) words += ' ';
            words += t[pos++];
        }
        if (words.empty())
            throw std::runtime_error("Se esperaba una proposicion simple cerca de " + here() + ".");
        return Formula::Atom(at.get(words));
    }
};

static FP parseRule(const string& text, AtomTable& at) {
    vector<string> tk = tokenize(normalizeWords(text));
    if (tk.empty()) throw std::runtime_error("La regla esta vacia.");
    Parser p(tk, at);
    FP f = p.parseIff();
    if (p.pos != tk.size()) throw std::runtime_error("No pude interpretar la regla cerca de " + p.here() + ".");
    return f;
}

// ----------------------------------------------------------------------------
//  Tableau
// ----------------------------------------------------------------------------
struct Item {
    FP f;
    bool applied;
    string label;
    Item(FP f_, const string& l = "") : f(std::move(f_)), applied(false), label(l) {}
};

struct TNode {
    vector<Item> items;
    vector<shared_ptr<TNode>> children;
    bool closed = false, open = false;
    string closeInfo;
    // layout
    float cx = 0, top = 0, w = 0, h = 0, sw = 0;
};
using NP = shared_ptr<TNode>;

enum Kind { LITERAL, ALPHA, BETA };

static Kind classify(const FP& f) {
    using F = Formula;
    switch (f->type) {
        case F::ATOM: return LITERAL;
        case F::AND: return ALPHA;
        case F::OR: case F::IMPLIES: case F::IFF: return BETA;
        case F::NOT:
            switch (f->left->type) {
                case F::ATOM: return LITERAL;
                case F::NOT: case F::OR: case F::IMPLIES: return ALPHA;  // ¬¬, ¬∨, ¬→
                case F::AND: case F::IFF: return BETA;                   // ¬∧, ¬↔
            }
    }
    return LITERAL;
}

// Resultado: una lista de ramas; cada rama es la lista de formulas que se agregan.
static vector<vector<FP>> expandFormula(const FP& f) {
    using F = Formula;
    using V = vector<FP>;
    auto N = [](const FP& x) { return F::Not(x); };
    vector<V> r;
    switch (f->type) {
        case F::AND:     r.push_back(V{f->left, f->right}); break;
        case F::OR:      r.push_back(V{f->left}); r.push_back(V{f->right}); break;
        case F::IMPLIES: r.push_back(V{N(f->left)}); r.push_back(V{f->right}); break;
        case F::IFF:     r.push_back(V{f->left, f->right}); r.push_back(V{N(f->left), N(f->right)}); break;
        case F::NOT: {
            const FP& g = f->left;
            switch (g->type) {
                case F::NOT:     r.push_back(V{g->left}); break;
                case F::OR:      r.push_back(V{N(g->left), N(g->right)}); break;
                case F::IMPLIES: r.push_back(V{g->left, N(g->right)}); break;
                case F::AND:     r.push_back(V{N(g->left)}); r.push_back(V{N(g->right)}); break;
                case F::IFF:     r.push_back(V{g->left, N(g->right)}); r.push_back(V{N(g->left), g->right}); break;
                default: break;
            }
            break;
        }
        default: break;
    }
    return r;
}

// Expande una rama (path = nodos desde la raiz hasta la hoja `leaf`)
static void expandBranch(const NP& leaf, vector<TNode*>& path) {
    while (true) {
        // 1) cierre: un atomo y su negacion en la rama
        std::set<string> lits;
        for (TNode* n : path)
            for (auto& it : n->items) {
                string k;
                if (literalKey(it.f, k)) lits.insert(k);
            }
        for (const auto& k : lits)
            if (k[0] != '~' && lits.count("~" + k)) {
                leaf->closed = true;
                leaf->closeInfo = k + " / " + symNot() + k;
                return;
            }

        // 2) buscar formula sin aplicar (primero las alfa, luego las beta)
        Item* target = nullptr;
        for (int pass = 0; pass < 2 && !target; ++pass) {
            Kind want = pass == 0 ? ALPHA : BETA;
            for (TNode* n : path) {
                for (auto& it : n->items)
                    if (!it.applied && classify(it.f) == want) { target = &it; break; }
                if (target) break;
            }
        }
        if (!target) { leaf->open = true; return; }  // solo quedan literales

        target->applied = true;
        FP f = target->f;  // copia (el puntero puede invalidarse al agregar items)
        auto br = expandFormula(f);

        if (br.size() == 1) {  // regla alfa: se agrega en la misma rama
            for (auto& g : br[0]) leaf->items.push_back(Item(g));
        } else {               // regla beta: la rama se bifurca
            for (auto& b : br) {
                auto c = std::make_shared<TNode>();
                for (auto& g : b) c->items.push_back(Item(g));
                leaf->children.push_back(c);
            }
            for (auto& c : leaf->children) {
                path.push_back(c.get());
                expandBranch(c, path);
                path.pop_back();
            }
            return;
        }
    }
}

struct Model { std::map<string, bool> val; };

static void collectLeaves(const NP& n, vector<TNode*>& path, vector<Model>& models,
                          int& nClosed, int& nOpen) {
    path.push_back(n.get());
    if (n->children.empty()) {
        if (n->closed) nClosed++;
        else {
            nOpen++;
            Model m;
            for (TNode* p : path)
                for (auto& it : p->items) {
                    string k;
                    if (literalKey(it.f, k)) {
                        if (k[0] == '~') m.val[k.substr(1)] = false;
                        else m.val[k] = true;
                    }
                }
            models.push_back(m);
        }
    } else {
        for (auto& c : n->children) collectLeaves(c, path, models, nClosed, nOpen);
    }
    path.pop_back();
}

// ----------------------------------------------------------------------------
//  Layout y dibujo
// ----------------------------------------------------------------------------
static const float ITEM_H = 24, V_GAP = 36, H_GAP = 18;

static float textW(const string& s, unsigned size) {
    sf::Text t;
    t.setFont(gFontSym);
    t.setString(U(s));
    t.setCharacterSize(size);
    return t.getLocalBounds().width;
}

static string itemStr(const Item& it) {
    string s = it.label.empty() ? "" : it.label + ": ";
    s += it.f->str();
    if (it.applied) s += string(" ") + symOk();
    return s;
}

static string markerStr(const TNode* n) {
    if (n->closed) return string(symX()) + " CERRADA (" + n->closeInfo + ")";
    return "ABIERTA";
}

static void measure(TNode* n) {
    float w = 90;
    for (auto& it : n->items) w = std::max(w, textW(itemStr(it), 14) + 18);
    float h = n->items.size() * ITEM_H;
    if (n->closed || n->open) {
        w = std::max(w, textW(markerStr(n), 13) + 18);
        h += 22;
    }
    n->w = w;
    n->h = h;
    float sum = 0;
    for (auto& c : n->children) { measure(c.get()); sum += c->sw; }
    if (n->children.size() > 1) sum += H_GAP * (n->children.size() - 1);
    n->sw = std::max(w, sum);
}

static void place(TNode* n, float left, float top, float& maxBottom) {
    n->cx = left + n->sw / 2;
    n->top = top;
    maxBottom = std::max(maxBottom, top + n->h);
    if (n->children.empty()) return;
    float total = 0;
    for (auto& c : n->children) total += c->sw;
    total += H_GAP * (n->children.size() - 1);
    float cl = left + (n->sw - total) / 2;
    for (auto& c : n->children) {
        place(c.get(), cl, top + n->h + V_GAP, maxBottom);
        cl += c->sw + H_GAP;
    }
}

static float drawText(sf::RenderTarget& rt, const sf::Font& f, const string& s, float x, float y,
                      unsigned size, sf::Color c, bool bold = false) {
    sf::Text t;
    t.setFont(f);
    t.setString(U(s));
    t.setCharacterSize(size);
    t.setFillColor(c);
    if (bold) t.setStyle(sf::Text::Bold);
    t.setPosition(x, y);
    rt.draw(t);
    return size + 7.0f;
}

static void drawNode(sf::RenderTarget& rt, const TNode* n) {
    float left = n->cx - n->w / 2;
    sf::Color bg = n->closed ? sf::Color(255, 205, 205)
                 : n->open   ? sf::Color(200, 240, 200)
                             : sf::Color(232, 232, 232);
    for (size_t i = 0; i < n->items.size(); ++i) {
        const Item& it = n->items[i];
        float y = n->top + i * ITEM_H;
        sf::RectangleShape box(sf::Vector2f(n->w, ITEM_H - 2));
        box.setPosition(left, y);
        box.setFillColor(bg);
        box.setOutlineColor(sf::Color(150, 150, 150));
        box.setOutlineThickness(1);
        rt.draw(box);
        sf::Color tc = it.applied ? sf::Color(110, 110, 110) : sf::Color::Black;
        drawText(rt, gFontSym, itemStr(it), left + 8, y + 2, 14, tc);
    }
    float y = n->top + n->items.size() * ITEM_H;
    if (n->closed)
        drawText(rt, gFontSym, markerStr(n), left + 8, y + 2, 13, sf::Color(200, 0, 0), true);
    else if (n->open)
        drawText(rt, gFontSym, markerStr(n), left + 8, y + 2, 13, sf::Color(0, 130, 0), true);

    for (const auto& c : n->children) {
        sf::Vertex line[2] = {sf::Vertex(sf::Vector2f(n->cx, n->top + n->h), sf::Color(0, 0, 200)),
                              sf::Vertex(sf::Vector2f(c->cx, c->top), sf::Color(0, 0, 200))};
        rt.draw(line, 2, sf::Lines);
        drawNode(rt, c.get());
    }
}

// ----------------------------------------------------------------------------
//  Utilidades de texto de interfaz
// ----------------------------------------------------------------------------
static vector<string> wrapText(const string& s, const sf::Font& font, unsigned size, float maxW) {
    vector<string> lines;
    std::istringstream is(s);
    string w, cur;
    sf::Text t;
    t.setFont(font);
    t.setCharacterSize(size);
    while (is >> w) {
        string trial = cur.empty() ? w : cur + " " + w;
        t.setString(U(trial));
        if (t.getLocalBounds().width > maxW && !cur.empty()) { lines.push_back(cur); cur = w; }
        else cur = trial;
    }
    if (!cur.empty()) lines.push_back(cur);
    if (lines.empty()) lines.push_back("");
    return lines;
}

static string capitalize(string s) {
    if (!s.empty()) s[0] = static_cast<char>(std::toupper(static_cast<unsigned char>(s[0])));
    return s;
}

// Pasa un codepoint Unicode (acentuado) a ASCII; 0 si no se puede
static char foldCodepoint(sf::Uint32 c) {
    switch (c) {
        case 0xE1: case 0xE0: case 0xE2: case 0xE4: case 0xE3:
        case 0xC1: case 0xC0: case 0xC2: case 0xC4: case 0xC3: return 'a';
        case 0xE9: case 0xE8: case 0xEA: case 0xEB:
        case 0xC9: case 0xC8: case 0xCA: case 0xCB: return 'e';
        case 0xED: case 0xEC: case 0xEE: case 0xEF:
        case 0xCD: case 0xCC: case 0xCE: case 0xCF: return 'i';
        case 0xF3: case 0xF2: case 0xF4: case 0xF6: case 0xF5:
        case 0xD3: case 0xD2: case 0xD4: case 0xD6: case 0xD5: return 'o';
        case 0xFA: case 0xF9: case 0xFB: case 0xFC:
        case 0xDA: case 0xD9: case 0xDB: case 0xDC: return 'u';
        case 0xF1: case 0xD1: return 'n';
        default: return 0;
    }
}

static string modelStr(const Model& m, const AtomTable& at) {
    string s;
    for (const auto& a : at.order) {
        if (!s.empty()) s += ", ";
        auto it = m.val.find(a.first);
        s += a.first + " = " + (it == m.val.end() ? "V o F (libre)" : it->second ? "V" : "F");
    }
    return s;
}

// ----------------------------------------------------------------------------
//  Estado de la aplicacion
// ----------------------------------------------------------------------------
struct App {
    vector<string> rulesText;
    vector<FP> rulesF;
    AtomTable atoms;
    NP root;
    vector<Model> models;
    int nClosed = 0, nOpen = 0;
    float totalH = 0;

    void rebuild() {
        atoms = AtomTable();
        rulesF.clear();
        for (const auto& r : rulesText) rulesF.push_back(parseRule(r, atoms));

        root = std::make_shared<TNode>();
        for (size_t i = 0; i < rulesF.size(); ++i)
            root->items.push_back(Item(rulesF[i], "R" + std::to_string(i + 1)));
        vector<TNode*> path{root.get()};
        if (!rulesF.empty()) expandBranch(root, path);

        models.clear();
        nClosed = nOpen = 0;
        if (!rulesF.empty()) {
            vector<TNode*> p2;
            collectLeaves(root, p2, models, nClosed, nOpen);
        }
        measure(root.get());
        totalH = 0;
        place(root.get(), 0, 0, totalH);
    }

    bool addRule(const string& text, string& err) {
        AtomTable tmp = atoms;
        try { parseRule(text, tmp); }
        catch (const std::exception& e) { err = e.what(); return false; }
        rulesText.push_back(text);
        rebuild();
        return true;
    }
};

// ----------------------------------------------------------------------------
//  Barra lateral (contenido con scroll). Devuelve la altura total del contenido.
// ----------------------------------------------------------------------------
static float drawSidebar(sf::RenderTarget& rt, const App& app, float sideW) {
    const sf::Color blue(0, 32, 96), gray(90, 90, 90);
    float y = 12;
    float maxW = sideW - 40;

    y += drawText(rt, gFontText, "Base de conocimiento", 20, y, 18, blue, true) + 6;
    if (app.rulesText.empty())
        y += drawText(rt, gFontText, "(sin reglas todavia)", 20, y, 13, gray);
    for (size_t i = 0; i < app.rulesText.size(); ++i) {
        for (const auto& ln : wrapText(app.rulesText[i], gFontText, 13, maxW))
            y += drawText(rt, gFontText, ln, 20, y, 13, gray) - 2;
        y += drawText(rt, gFontSym, "R" + std::to_string(i + 1) + ": " + app.rulesF[i]->str(),
                      20, y, 15, blue, true);
        y += 6;
    }

    y += 8;
    y += drawText(rt, gFontText, "Tabla de atomos", 20, y, 18, blue, true) + 4;
    for (const auto& a : app.atoms.order) {
        string line = a.first + "  :  " + capitalize(a.second);
        for (const auto& ln : wrapText(line, gFontText, 14, maxW - 10))
            y += drawText(rt, gFontText, ln, 30, y, 14, sf::Color::Black);
    }

    y += 8;
    y += drawText(rt, gFontText, "Resultado", 20, y, 18, blue, true) + 4;
    if (app.rulesText.empty()) {
        y += drawText(rt, gFontText, "Agrega reglas para construir el arbol.", 20, y, 13, gray);
    } else {
        string head = "Ramas cerradas: " + std::to_string(app.nClosed) +
                      "   |   abiertas: " + std::to_string(app.nOpen);
        y += drawText(rt, gFontText, head, 20, y, 13, sf::Color::Black);
        if (app.nOpen == 0) {
            for (const auto& ln : wrapText("Todas las ramas se cierran: la base de conocimiento es "
                                           "INSATISFACIBLE (no existe ningun modelo que haga "
                                           "verdaderas todas las reglas).", gFontText, 13, maxW))
                y += drawText(rt, gFontText, ln, 20, y, 13, sf::Color(200, 0, 0), true);
        } else {
            y += drawText(rt, gFontText, "SATISFACIBLE. Condiciones en que todas las reglas se cumplen:",
                          20, y, 13, sf::Color(0, 120, 0), true);
            for (size_t i = 0; i < app.models.size(); ++i) {
                string s = "Rama abierta " + std::to_string(i + 1) + ": " + modelStr(app.models[i], app.atoms);
                for (const auto& ln : wrapText(s, gFontSym, 14, maxW))
                    y += drawText(rt, gFontSym, ln, 20, y, 14, sf::Color::Black);
                y += 4;
            }
        }
    }
    return y + 20;
}

// ----------------------------------------------------------------------------
//  main
// ----------------------------------------------------------------------------
int main() {
    if (!loadFonts()) {
        std::cerr << "Error: no se encontro ninguna fuente (arial.ttf). "
                     "Copia arial.ttf junto al .exe o revisa C:/Windows/Fonts.\n";
        return 1;
    }

    sf::RenderWindow window(sf::VideoMode(1400, 800), "Arbol Semantico - Logica Proposicional",
                            sf::Style::Default);
    window.setFramerateLimit(60);

    const float SIDEBAR = 380, HEADER = 78, INPUT_H = 130;

    App app;
    app.rulesText = {"Si es de dia, entonces voy a trabajar",
                     "Si llueve, entonces no voy a trabajar",
                     "Es de dia"};
    app.rebuild();

    string userInput, errMsg;
    float sideScroll = 0, sideContentH = 0;
    float zoom = 1.0f;
    sf::Vector2f center(0, 0);
    bool dragging = false;
    sf::Vector2i lastMouse;
    sf::Clock blink;

    auto fitView = [&]() {
        sf::Vector2u sz = window.getSize();
        float areaW = sz.x - SIDEBAR, areaH = sz.y - HEADER;
        zoom = std::max(1.0f, std::max((app.root->sw + 40) / areaW, (app.totalH + 30) / areaH));
        center = sf::Vector2f(app.root->cx, zoom * areaH / 2 - 10 * zoom);
    };
    fitView();

    while (window.isOpen()) {
        sf::Event event;
        while (window.pollEvent(event)) {
            if (event.type == sf::Event::Closed) window.close();

            else if (event.type == sf::Event::TextEntered) {
                sf::Uint32 c = event.text.unicode;
                if (c == '\b') {
                    if (!userInput.empty()) userInput.pop_back();
                    errMsg.clear();
                } else if (c == '\r' || c == '\n') {
                    if (!userInput.empty()) {
                        string err;
                        if (app.addRule(userInput, err)) {
                            userInput.clear();
                            errMsg.clear();
                            fitView();
                        } else errMsg = err;
                    }
                } else if (c >= 32 && c < 127) {
                    userInput += static_cast<char>(c);
                    errMsg.clear();
                } else if (char f = foldCodepoint(c)) {
                    userInput += f;
                    errMsg.clear();
                }
            }
            else if (event.type == sf::Event::KeyPressed) {
                if (event.key.code == sf::Keyboard::Delete && !app.rulesText.empty()) {
                    app.rulesText.pop_back();
                    app.rebuild();
                    fitView();
                } else if (event.key.code == sf::Keyboard::Home) {
                    fitView();
                }
            }
            else if (event.type == sf::Event::MouseButtonPressed &&
                     event.mouseButton.button == sf::Mouse::Left) {
                if (event.mouseButton.x >= SIDEBAR && event.mouseButton.y >= HEADER) {
                    dragging = true;
                    lastMouse = sf::Vector2i(event.mouseButton.x, event.mouseButton.y);
                }
            }
            else if (event.type == sf::Event::MouseButtonReleased) {
                dragging = false;
            }
            else if (event.type == sf::Event::MouseMoved) {
                if (dragging) {
                    sf::Vector2i cur(event.mouseMove.x, event.mouseMove.y);
                    center.x -= (cur.x - lastMouse.x) * zoom;
                    center.y -= (cur.y - lastMouse.y) * zoom;
                    lastMouse = cur;
                }
            }
            else if (event.type == sf::Event::MouseWheelScrolled) {
                if (event.mouseWheelScroll.x < SIDEBAR) sideScroll -= event.mouseWheelScroll.delta * 40;
                else {
                    zoom *= event.mouseWheelScroll.delta > 0 ? 0.9f : 1.1f;
                    zoom = std::max(0.2f, std::min(6.0f, zoom));
                }
            }
        }

        sf::Vector2u sz = window.getSize();
        float W = static_cast<float>(sz.x), H = static_cast<float>(sz.y);
        sf::View full(sf::FloatRect(0, 0, W, H));

        window.clear(sf::Color::White);

        // ---------- Arbol (zona derecha, con zoom y arrastre) ----------
        if (!app.rulesText.empty()) {
            float areaW = W - SIDEBAR, areaH = H - HEADER;
            sf::View treeView;
            treeView.setViewport(sf::FloatRect(SIDEBAR / W, HEADER / H, areaW / W, areaH / H));
            treeView.setSize(areaW * zoom, areaH * zoom);
            treeView.setCenter(center);
            window.setView(treeView);
            drawNode(window, app.root.get());
        }

        // ---------- Cabecera ----------
        window.setView(full);
        {
            sf::RectangleShape hb(sf::Vector2f(W - SIDEBAR, HEADER));
            hb.setPosition(SIDEBAR, 0);
            hb.setFillColor(sf::Color::White);
            window.draw(hb);
            drawText(window, gFontText, "Tableau semantico (arbol de verdad)", SIDEBAR + 20, 10, 18,
                     sf::Color(0, 32, 96), true);
            string res; sf::Color rc = sf::Color::Black;
            if (app.rulesText.empty()) res = "Escribe reglas en espanol para comenzar.";
            else if (app.nOpen == 0) {
                res = "Todas las ramas se cierran -> la base de conocimiento es INSATISFACIBLE.";
                rc = sf::Color(200, 0, 0);
            } else {
                res = std::to_string(app.nClosed) + " rama(s) cerrada(s), " + std::to_string(app.nOpen) +
                      " abierta(s) -> base SATISFACIBLE.";
                rc = sf::Color(0, 120, 0);
            }
            drawText(window, gFontText, res, SIDEBAR + 20, 38, 14, rc, true);
            drawText(window, gFontSym,
                     string("verde = rama abierta  |  rojo = rama cerrada  |  ") + symOk() +
                         " = formula aplicada  |  rueda = zoom  |  arrastrar = mover  |  Inicio = recentrar",
                     SIDEBAR + 20, 58, 11, sf::Color(110, 110, 110));
        }

        // ---------- Barra lateral ----------
        {
            sf::RectangleShape sb(sf::Vector2f(SIDEBAR, H));
            sb.setFillColor(sf::Color(240, 240, 240));
            window.draw(sb);

            float viewH = H - INPUT_H;
            sideScroll = std::max(0.0f, std::min(sideScroll, std::max(0.0f, sideContentH - viewH)));
            sf::View content;
            content.setViewport(sf::FloatRect(0, 0, SIDEBAR / W, viewH / H));
            content.setSize(SIDEBAR, viewH);
            content.setCenter(SIDEBAR / 2, sideScroll + viewH / 2);
            window.setView(content);
            sideContentH = drawSidebar(window, app, SIDEBAR);
        }

        // ---------- Entrada de texto ----------
        window.setView(full);
        {
            float y0 = H - INPUT_H;
            sf::RectangleShape pan(sf::Vector2f(SIDEBAR, INPUT_H));
            pan.setPosition(0, y0);
            pan.setFillColor(sf::Color(225, 228, 235));
            window.draw(pan);

            drawText(window, gFontText, "Escribe una regla (Enter = anadir, Supr = borrar la ultima):",
                     12, y0 + 6, 12, sf::Color(0, 32, 96));
            sf::RectangleShape ib(sf::Vector2f(SIDEBAR - 24, 30));
            ib.setPosition(12, y0 + 28);
            ib.setFillColor(sf::Color::White);
            ib.setOutlineColor(sf::Color::Blue);
            ib.setOutlineThickness(1);
            window.draw(ib);

            string shown = userInput + ((static_cast<int>(blink.getElapsedTime().asSeconds() * 2) % 2) ? "" : "_");
            while (shown.size() > 1 && textW(shown, 14) > SIDEBAR - 44) shown.erase(0, 1);
            drawText(window, gFontText, shown, 18, y0 + 34, 14, sf::Color::Black);

            float ey = y0 + 66;
            if (!errMsg.empty())
                for (const auto& ln : wrapText(errMsg, gFontText, 12, SIDEBAR - 24))
                    ey += drawText(window, gFontText, ln, 12, ey, 12, sf::Color(200, 0, 0)) - 3;
            else
                drawText(window, gFontText,
                         "Conectivos: y, o, no, si ... entonces, si y solo si", 12, ey, 11,
                         sf::Color(100, 100, 100));
        }

        window.display();
    }
    return 0;
}