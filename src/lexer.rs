use crate::Error;
use logos::Logos;
use offsides::{Layout, LayoutConfig, LayoutLexer, LayoutMode, OpenerRule};
use std::fmt;

const TAB_WIDTH: usize = 4;

#[derive(Logos, Clone, Debug, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n\f]+")]
#[logos(skip(r"--[^\r\n]*", allow_greedy = true))]
pub enum Token {
    #[token("axiom")]
    Axiom,
    #[token("def")]
    Def,
    #[token("theorem")]
    Theorem,
    #[token("inductive")]
    Inductive,
    #[token("init_quot")]
    InitQuot,
    #[token("proj")]
    Proj,
    #[token("succ")]
    Succ,
    #[token("max")]
    Max,
    #[token("imax")]
    IMax,
    #[token("infer")]
    Infer,
    #[token("check")]
    Check,
    #[token("eval")]
    Eval,
    #[token("equal")]
    Equal,
    #[token("fun")]
    #[token("λ")]
    Fun,
    #[token("forall")]
    #[token("∀")]
    Forall,
    #[token("let")]
    Let,
    #[token("in")]
    In,
    #[token("Prop")]
    Prop,
    #[token("Type")]
    Type,
    #[token("Sort")]
    Sort,
    #[token("->")]
    #[token("→")]
    Arrow,
    #[token("=>")]
    FatArrow,
    #[token(":=")]
    Assign,
    #[token("==")]
    EqEq,
    #[token(":")]
    Colon,
    #[token(",")]
    Comma,
    #[token(";")]
    Semi,
    #[token("@")]
    At,
    #[token("|")]
    Bar,
    #[token("+")]
    Plus,
    #[token(".{")]
    DotBrace,
    #[token("}")]
    RBrace,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[regex(r"[0-9]+", |l| l.slice().to_owned())]
    Num(String),
    #[regex(r#""([^"\\]|\\.)*""#, |l| serde_json::from_str::<String>(l.slice()).ok())]
    Str(String),
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_']*(\.[a-zA-Z_][a-zA-Z0-9_']*)*", |l| l.slice().to_owned())]
    Ident(String),
    VOpen,
    VClose,
    VSep,
}

impl Layout for Token {
    fn v_open() -> Self {
        Self::VOpen
    }
    fn v_close() -> Self {
        Self::VClose
    }
    fn v_sep() -> Self {
        Self::VSep
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ident(n) | Self::Num(n) => f.write_str(n),
            Self::Str(s) => write!(f, "{s:?}"),
            _ => write!(f, "{self:?}"),
        }
    }
}

pub fn lex(
    source: &str,
    mode: LayoutMode,
) -> impl Iterator<Item = Result<(usize, Token, usize), Error>> + '_ {
    let raw = Token::lexer(source).spanned().map(|(t, span)| {
        t.map(|t| (span.start, t, span.end))
            .map_err(|_| Error(format!("invalid token at byte {}", span.start)))
    });
    let config = LayoutConfig::new(|t| matches!(t, Token::Let))
        .with_mode(mode)
        .with_opener_rule(OpenerRule::Conditional)
        .with_brackets(
            |t| matches!(t, Token::LParen),
            |t| matches!(t, Token::RParen),
        )
        .with_tab_width(TAB_WIDTH);
    LayoutLexer::new(raw, source, config)
}
