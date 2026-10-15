# Writing rigorous mathematics papers that referees and editors accept (with a JSTAT / physics-audience focus), and handling rejection and resubmission

Verification key: **[V]** means I read the quote in the primary text during this session. **[S]** means it comes from a search-engine summary of the page, not my own reading, so check it before quoting. **[UNVERIFIED, memory]** means it comes from my training memory with no source checked this session.

Primary texts I actually read: Halmos 1970 (full text extracted from PDF), Pak 2018 (full text extracted from PDF), Tao's advice pages (index, "describe results accurately", "use the introduction to sell", "submit to an appropriate journal"), and IOP's Generative AI policy page. Pages I could not open: Serre transcript (404), JSTAT referee-guidelines PDF (the server returned an unrelated PDF), JSTAT "About" page (bot wall), Mermin column (PDF-only).

---

## (1) Structure and introduction

### Takeaway
Put the main theorem, or an easy-to-state corollary of it, on page 1 or 2 of the introduction. Place it explicitly against prior work (what [A] did, what [B] did, what this paper adds). End the introduction with a roadmap. Write the introduction first, then rewrite it completely once the paper is finished. Put long history and speculation in a "Final Remarks" section rather than the introduction.

### Cited Findings
- Tao: the introduction should "clearly state (or at least paraphrase) the main results of the paper", should "spend some time comparing and contrasting the paper to other literature", and should "demonstrate why the paper's results and techniques are new, interesting, and/or surprising given this context" [V]. — [Tao, Use the introduction to "sell" the key points](https://terrytao.wordpress.com/advice-on-writing-papers/use-the-introduction-to-%E2%80%9Csell%E2%80%9D-the-key-points-of-your-paper/)
- Tao: the introduction "ideally should also outline how and where these results are to be proved". If the main result is too technical, "a simpler (but still interesting) special case can be stated instead". An informal statement is fine if "it should be clearly indicated that that this statement is informal" [V]. — [same](https://terrytao.wordpress.com/advice-on-writing-papers/use-the-introduction-to-%E2%80%9Csell%E2%80%9D-the-key-points-of-your-paper/)
- Pak: the introduction "is the hardest section to write. It's probably the only part of your paper that will be read by all but a few most devoted readers." He advises: "Start writing your paper by writing the first draft of the Introduction ... and completely rewrite it after the rest of the paper is written" [V]. — [Pak, How to write a clear math paper (J. Humanistic Math. 8 (2018))](https://www.math.ucla.edu/~pak/papers/how-to-write1.pdf)
- Pak: "do aim to have your first theorem on the first page, or at worst on the second page." If the main theorem is too technical, "include interesting, nontrivial, but easy to state corollaries ... Cook them up if necessary and think of them as an advertisement of your paper" [V]. — [Pak](https://www.math.ucla.edu/~pak/papers/how-to-write1.pdf)
- Pak's model history paragraph: "Paper [A] asked about XYZ and proved weak-XYZ. Last year, paper [B] showed that strong-XYZ is false. In this paper we refine the tools in [B] to show..." He says to ignore Rota's advice about "giving everybody his due". Only directly relevant papers belong in the introduction, and "The rest are cited in the Final Remarks" [V]. — [Pak](https://www.math.ucla.edu/~pak/papers/how-to-write1.pdf)
- Pak, what not to include in the introduction: "Technical definitions, examples, big figures ... Instead ... use '(see Figure 5.1)' or '(see the exact definition in §3.4)'." On the roadmap: "In the last paragraph or subsection of the Introduction, outline the structure of the paper" [V]. — [Pak](https://www.math.ucla.edu/~pak/papers/how-to-write1.pdf)
- Pak, the Foreword: if the introduction runs past about 4 pages, open it with a short nontechnical "Foreword" that can mention "general physical or philosophical principles underlying your work"; "I doubt referees would object if you keep your Foreword under one page" [V]. This is relevant for giving physical motivation in a mathematical paper. — [Pak](https://www.math.ucla.edu/~pak/papers/how-to-write1.pdf)
- Pak: the Final Remarks section should be divided into short untitled subsections that hold history, extensions and open problems. He reports that referees sometimes object to its size, for example "to each paragraph makes this last section feel very disjointed," wrote one referee [V]. — [Pak](https://www.math.ucla.edu/~pak/papers/how-to-write1.pdf)
- Halmos: "Write in spirals." Under the "spiral plan", earlier sections are rewritten every time a later one is drafted. Halmos argues this is unavoidable because you only understand Section 2 after writing Section 4 [V]. — [Halmos, How to Write Mathematics (1970)](https://faculty.washington.edu/heagerty/Courses/b572/public/HalmosHowToWrite.pdf)
- Halmos: "you must have something to say, and you must have someone to say it to" ("Say something", "Speak to someone"). On audience: "what varies is the amount of motivation you need to put in ... the fussiness of the detail ... and the number of times things have to be repeated" [V]. — [Halmos](https://faculty.washington.edu/heagerty/Courses/b572/public/HalmosHowToWrite.pdf)
- Tao lists further pages: "Organise the paper", "Motivate the paper", "Create lemmas", "Write a rapid prototype first", "Don't over-optimise" [V, titles only]. — [Tao, Advice on writing papers](https://terrytao.wordpress.com/advice-on-writing-papers/)
- Whitesides: write the paper from an outline that you keep reworking as the project goes. He is quoted as saying "All the writing that I do—papers, reports, proposals ... I do from outlines" [S, secondary summary]. — [Editage summary](https://www.editage.com/insights/a-3-page-guide-to-scientific-writing); original: [Whitesides group page](https://gmwgroup.harvard.edu/publications/whitesides-group-writing-paper)

### Inferences
- For a math paper in a stat-mech journal, the Tao/Pak structure becomes: physical motivation (a short Foreword-style paragraph) → precise main theorem on page 1–2 → explicit comparison with the physics literature (what was heuristic or numerical before, what is now proved) → roadmap.

### Gaps
- I did not read Whitesides' original PDF, so I have no verbatim quotes from it.

---

## (2) Stating results and proofs

### Takeaway
State each theorem before its proof, with only the hypotheses it needs. Do not overclaim, and do not underclaim. Say openly which hypotheses may be unnecessary and which steps are only sketched. Break proofs into lemmas. Handle trivial and degenerate cases explicitly rather than leaving them "legalistically correct".

### Cited Findings
- Tao: "A paper should neither understate nor overstate its main results." Weaknesses such as overly strong hypotheses "should also be stated honestly and openly", for example "We do not know if hypothesis H is actually necessary". When the motivation is a famous conjecture, give a candid account of how much progress this really is. Mark unproved claims, for example with "It can be shown that…" [V]. — [Tao, Describe the results accurately](https://terrytao.wordpress.com/advice-on-writing-papers/describe-the-results-accurately/)
- Tao: "factor the paper into smaller pieces, for instance by making plenty of lemmas" [V, via index summary]. — [Tao, Create lemmas](https://terrytao.wordpress.com/advice-on-writing-papers/create-lemmas/)
- Halmos on where to state theorems: "my answer is: first. Don't ramble on in a leisurely way ... and then suddenly announce 'Thus we have proved that ...'." Stating it first helps because the reader "can see better where the hypotheses are used if he knows in advance what they are." He calls the alternative the "hanging" theorem, "which I think is ugly" [V]. — [Halmos](https://faculty.washington.edu/heagerty/Courses/b572/public/HalmosHowToWrite.pdf)
- Halmos: "there, more than anywhere else, irrelevancies must be avoided." Elsewhere: "Irrelevant assumptions wantonly dragged in, incorrect emphasis ... can wreak havoc" [V]. — [Halmos](https://faculty.washington.edu/heagerty/Courses/b572/public/HalmosHowToWrite.pdf)
- Halmos on trivial cases: the author should gain "the reader's confidence by explicitly mentioning trivial cases and excluding them if need be". "Legalistically correct but insufficiently explicit explanations ('The statement is correct as it stands — what else do you want?') is misleading, bad exposition, bad psychology" [V]. — [Halmos](https://faculty.washington.edu/heagerty/Courses/b572/public/HalmosHowToWrite.pdf)
- Halmos, "Honesty is the best policy": "take the reader into your confidence" and "Complete honesty makes for greatest clarity." He warns against being "cleverly dishonest and to gloss over difficulties" [V]. — [Halmos](https://faculty.washington.edu/heagerty/Courses/b572/public/HalmosHowToWrite.pdf)
- Halmos on parallel results: "use the same words in the same order for as long as possible, and then, with a proper roll of drums, emphasize the difference" [V]. — [Halmos](https://faculty.washington.edu/heagerty/Courses/b572/public/HalmosHowToWrite.pdf)
- Tao, on reading papers: there are pages on "local and global errors" and on "the strength of theorems and jumps in difficulty". These describe how referees hunt for errors, which makes them a useful self-check [V, titles only]. — [Tao index](https://terrytao.wordpress.com/advice-on-writing-papers/)
- Tao: "Proofread and double-check before submission" and "Submit a final draft, not a first draft" [V, titles only]. — [Tao index](https://terrytao.wordpress.com/advice-on-writing-papers/)

### Inferences
- In a physics journal, explicitly separate "Theorem (proved)" from "Conjecture / heuristic / numerical observation". This is Tao's honest-description rule in its stat-mech form. Physics referees often assume a mathematician overclaims "physical" consequences, so state precisely which limits (thermodynamic limit, order of limits) and which boundary conditions the theorem covers.

### Gaps
- Serre's "How to write mathematics badly" (Harvard, 2003): the transcript URL returned 404. A course handout reports that his rule 1 is to not use mathematical symbols as verbs [S]. — [Lombardo, Pisa, Style.pdf](https://people.dm.unipi.it/lombardo/files/Style.pdf). His other points are [UNVERIFIED, memory]: he objects to long chains of hypotheses ("Let X be ... let Y be ..."), and he jokes that a "bad" writer avoids the reader-friendly practice of restating hypotheses inside theorems.

---

## (3) Notation and exposition

### Takeaway
Design the notation globally, before or after drafting, not mid-sentence. Use as few symbols as possible and none that appear only once. Do not start sentences with symbols. Keep a term's exact wording fixed once it is defined. Repeating things is fine, and reminding readers of notation helps them.

### Cited Findings
- Halmos: "The best notation is no notation; whenever it is possible to avoid the use of a complicated alphabetic apparatus, avoid it." Imagine "explaining the subject to a friend on a long walk in the woods" [V]. — [Halmos §15 "Resist symbols"](https://faculty.washington.edu/heagerty/Courses/b572/public/HalmosHowToWrite.pdf)
- Halmos: "use no letter only once ('leave no variable free')." Example: in "On a compact space every real-valued continuous function f is bounded", the symbol f contributes nothing [V]. — [Halmos](https://faculty.washington.edu/heagerty/Courses/b572/public/HalmosHowToWrite.pdf)
- Halmos: "Bad notation can make good exposition bad and bad exposition worse; ad hoc decisions about notation, made mid-sentence in the heat of composition, are almost certain to result in bad notation." He builds "huge tables with many alphabets" in advance [V]. — [Halmos](https://faculty.washington.edu/heagerty/Courses/b572/public/HalmosHowToWrite.pdf)
- Halmos: "never start a sentence with a symbol" [V]. Also: let "we" mean "the author and the reader", and do not leave "given" dangling ("Not 'Given p, there is a q', but 'Given p, find q'") [V]. — [Halmos](https://faculty.washington.edu/heagerty/Courses/b572/public/HalmosHowToWrite.pdf)
- Pak's notation case: a busy reader skims and misses your "notation explanation", so "you should definitely spend these 30 min and fix the notation issue" [V]. — [Pak §1](https://www.math.ucla.edu/~pak/papers/how-to-write1.pdf)
- Pak, "Downshift your style": "it is perfectly ok to be repetitive and have ten therefore's and be clear." Also, "it is a good style to remind the reader of notation you introduced earlier." On terminology: "if you define a property 'nice graph', then do not use 'niceness of graphs imply...' Stick to basic forms" [V]. — [Pak §5.3](https://www.math.ucla.edu/~pak/papers/how-to-write1.pdf)
- Pak on LaTeX: "Create a ton of macros", so that notation can be changed globally at the end. Use placeholder macros "when you are unsure about the notation". Avoid look-alike letters (κ vs k, υ vs v) and "avoid Gothic fonts". Use letter mnemonics: functions get "tails" (f, g, φ), and i, j, k, ℓ, m, n are always integers [V]. — [Pak §5.4](https://www.math.ucla.edu/~pak/papers/how-to-write1.pdf)
- Pak: "Don't be pedantic" (§5.2) and "Do NOT trust LaTeX" (§5.5) [V, headings]. — [Pak](https://www.math.ucla.edu/~pak/papers/how-to-write1.pdf)
- Tao: "Use good notation" and "Give appropriate amounts of detail" [V, titles]. Separate pages discuss "implicit notational conventions" and "compilation errors in mathematical reading", meaning the points where a reader cannot parse a step. — [Tao index](https://terrytao.wordpress.com/advice-on-writing-papers/)
- Mermin, "What's wrong with these equations?" (Physics Today, Oct. 1989; reprinted in *Why Quark Rhymes with Pork*). A secondary summary gives the core rule as punctuating equations and treating them as part of the prose [S]. — [Physics Today listing](https://physicstoday.aip.org/opinion/whats-wrong-with-these-equations); [Substack summary](https://bucketoverflow.substack.com/p/december-2023-mermin-on-writing-physics)

### Inferences
- Notation is a particular risk for a math-for-physics paper because physicists' conventions differ (β, Z, ⟨·⟩, "≈" vs "∼", sign conventions for H). A notation table, or one early paragraph fixing conventions that match the standard physics literature for the model, applies the Halmos/Pak advice to the JSTAT audience.

### Gaps
- Mermin's specific rules [UNVERIFIED, memory]: "Fisher's rule" (number all displayed equations, so readers can refer to them), and refer to an equation by a descriptive phrase as well as its number (e.g. "the Gibbs relation (12)" rather than a bare "(12)"). The column itself is PDF-only and I did not verify it.
- Higham, *Handbook of Writing for the Mathematical Sciences* (SIAM, 3rd ed. 2020); Knuth–Larrabee–Roberts, *Mathematical Writing* (MAA Notes 14, 1989); Krantz, *A Primer of Mathematical Writing* (AMS, 2nd ed. 2017); Gillman, *Writing Mathematics Well* (MAA 1987); Kleiman's notes. I did not fetch any of these. From memory [UNVERIFIED]: Knuth's rules include "don't start a sentence with a symbol", "don't use the symbols ∴, ⇒, ∀, ∃ in running text; replace them by words", and keep two formulas apart by separating them with words. Higham advises defining every symbol and covers word choice and English usage. These are widely quoted, but I have not verified them this session.

---

## (4) Abstracts and titles

### Takeaway
The title should approximate the result itself ("All tennis balls are white", not "On tennis balls"). The abstract should be plain, factual and short, a dry statement of the main results, because indexing services often reproduce it verbatim.

### Cited Findings
- Pak on titles: it "shouldn't be too long, too short, too vague or generic (as in 'On some problems in group theory'), but should be the first approximation to contents of your paper" [V]. — [Pak §3.2](https://www.math.ucla.edu/~pak/papers/how-to-write1.pdf)
- Pak's tennis-ball rule, quoted from his MathOverflow answer: "If you prove that all tennis balls are white make the title 'All tennis balls are white'. If you prove that some tennis balls are white, title your note 'On white tennis balls' ... a counterexample, use 'Not all tennis balls are white'" [V]. — [Pak](https://www.math.ucla.edu/~pak/papers/how-to-write1.pdf); [MathOverflow 81128](https://mathoverflow.net/questions/81128)
- Pak on abstracts: "think of a short MathSciNet summary ... The abstract should have nothing personal, just dry facts about the results. State key results first ... Provide no details and no connections to other works unless absolutely necessary." "Large fraction of MathSciNet reviews are just the abstracts, so make it clear, precise, plain and uninventive." His rule of thumb: the number of abstract lines should be about "0.3–0.5 times the number of pages" [V]. — [Pak §3.3](https://www.math.ucla.edu/~pak/papers/how-to-write1.pdf)
- Pak suggests naming a cumbersome new object (for example "Munro permutations") so that the title conveys content. He notes that this "might raise some eyebrows of the referees" [V]. — [Pak](https://www.math.ucla.edu/~pak/papers/how-to-write1.pdf)
- Pak: skip a table of contents unless the paper is over 60 pages [V]. — [Pak §3.4](https://www.math.ucla.edu/~pak/papers/how-to-write1.pdf)

### Inferences
- For a physics journal, the abstract should also name the physical model and the physical quantity, for example "free energy of the ... model" or "rigorous proof of the conjectured exponent ...", because physicists search by model name rather than by theorem type.

### Gaps
- I did not find a JSTAT- or IOP-specific abstract word limit this session. Check the IOP author guidelines.

---

## (5) Writing mathematics for physicists (statistical-mechanics readers)

### Takeaway
I found only a little authoritative, sourced guidance specific to math-for-physics papers. JSTAT judges papers on scientific quality, originality, *relevance* and *comprehension* for a broad statistical-physics community. Its referee guidance reportedly says that work which is merely correct ("not wrong") is not enough. A rigorous paper therefore has to make the physical payoff explicit.

### Cited Findings
- JSTAT's acceptance criteria are reportedly "scientific quality, originality, relevance and comprehension", with a "strict quality filter". The referee guidance reportedly says routine or "not wrong" work is insufficient and asks referees to assess significance, originality, and what the manuscript adds over published material [S; the PDF could not be opened]. — [JSTAT referee guidelines](https://jstat.sissa.it/jstat/docs/referee_guidelines_JSTAT.pdf); [JSTAT About](https://iopscience.iop.org/1742-5468/page/about_the_journal)
- JSTAT's scope reportedly "aims at a broad statistical physics community" and is defined roughly by the fields of the "Statistical Physics" conferences [S]. — [JSTAT About](https://iopscience.iop.org/1742-5468/page/about_the_journal); [Wikipedia](https://en.wikipedia.org/wiki/Journal_of_Statistical_Mechanics:_Theory_and_Experiment)
- Halmos on audience: the amount of "motivation you need to put in" depends on who you are writing for [V]. — [Halmos](https://faculty.washington.edu/heagerty/Courses/b572/public/HalmosHowToWrite.pdf)
- Pak's Foreword is the place for "general physical or philosophical principles underlying your work" [V]. He also notes that physics papers have a different reference culture: physics papers "are champions at" abbreviating references, and "even omit the titles" [V]. — [Pak](https://www.math.ucla.edu/~pak/papers/how-to-write1.pdf)
- Mermin: physics readers expect equations to be integrated into the prose and punctuated [S]. — [Substack summary of Mermin](https://bucketoverflow.substack.com/p/december-2023-mermin-on-writing-physics)

### Inferences
- These recommendations come from synthesising the sources above, and none is directly sourced. (a) Lead with the physical question and the physicists' prior (heuristic, numerical or non-rigorous) answer, then state what is now rigorous. (b) Translate the theorem into physical quantities such as free energy, correlation length, exponents and phase diagrams. (c) Move long technical proofs to sections or appendices, and give a proof sketch or "strategy" section that a physicist can read. (d) Cite the physics literature (heuristic, replica, numerical) as well as the math literature, because JSTAT referees will often be physicists. (e) Explain why rigour matters here, for example by showing a heuristic prediction fails, or by pinning down the order of limits or a regime.
- Physical Review-type journals and J. Stat. Phys. have a mathematical-physics tradition, while JSTAT is more physics-community oriented. If a referee says "too mathematical / not of interest to physicists", the realistic re-targets are J. Stat. Phys., Annales Henri Poincaré, J. Math. Phys., Commun. Math. Phys., or Electron. J. Probab./Probab. Theory Relat. Fields, depending on content. This journal landscape is [UNVERIFIED, memory].

### Gaps
- I found no Physical Review, IOP or JSTAT editorial specifically on how mathematicians should write for physicists. A 2009–2010 PRL editorial on "accessibility" and Phys. Rev. "broad interest" criteria may exist [UNVERIFIED, memory, not located].
- I could not read Mermin's column verbatim.

---

## (6) What referees and editors look for; common rejection reasons

### Takeaway
Desk rejections are driven mostly by scope mismatch and insufficient novelty or significance. Rejections after review stem from flaws, unclear exposition or weak rationale. A rejection at a selective journal often reflects competition for limited space more than errors.

### Cited Findings
- Tao: "a positive rejection rate is to be expected if one is submitting to reputable journals." Journals may have "multiple competing submissions and a target number of papers or pages to accept", so "the paper with the less favorable reviews will be rejected." Editors can reject quickly when "a report comes in that is highly negative" [V]. — [Tao, Submit to an appropriate journal](https://terrytao.wordpress.com/advice-on-writing-papers/submit-to-an-appropriate-journal/)
- Tao: borderline submissions to very selective journals risk "a lengthy process, critical reviews holding the paper to a very high standard" [V]. — [same](https://terrytao.wordpress.com/advice-on-writing-papers/submit-to-an-appropriate-journal/)
- Empirical evidence, from one psychiatry journal rather than math or physics: a study of 898 rejection reports found that lack of novelty or being out of scope led desk rejections. Post-review rejections were driven by "inappropriate study designs, poor methodological descriptions, poor quality of writing, and weak study rationale" [S]. — [Indian J. Psychol. Med. study (SAGE)](https://journals.sagepub.com/doi/abs/10.1177/0253717620965845)
- JSTAT: work that is "not wrong" is not sufficient, and referees assess significance and originality [S]. — [JSTAT referee guidelines](https://jstat.sissa.it/jstat/docs/referee_guidelines_JSTAT.pdf)
- Pak: "Can't journals help? In a word, NO." Copy editors will not fix your clarity [V]. He also notes papers that "sometimes get rejected (who knew this was solved 20 years ago?)", meaning a missed prior literature [V]. — [Pak](https://www.math.ucla.edu/~pak/papers/how-to-write1.pdf)

### Inferences
- For a rigorous paper at a physics journal, the most likely referee objections are (i) "the result was known or expected in the physics literature; what is new?" and (ii) "too technical or not of interest to the readership". Both are relevance and comprehension failures under JSTAT's criteria, not correctness failures.

### Gaps
- I found no mathematics-specific quantitative survey of rejection reasons, such as an AMS Notices editor survey, in this session. The Springer/Elsevier editor surveys were not located. Evidence is otherwise practitioner blogs (low quality, not cited).

---

## (7) After a rejection: referee reports, revisions, re-targeting, cover letters

### Takeaway
Don't take the rejection personally. Treat the reports as free reviews and revise using them, because the same objections tend to recur at the next journal. Re-target realistically, usually less selective or better matched in scope. If you resubmit within the same publisher (IOP), you must disclose the prior rejection and list the changes. Do not resubmit essentially unchanged.

### Cited Findings
- Tao: "I recommend not taking a rejection of a paper personally". He advises to "use any feedback received to improve the exposition of the paper" and then resubmit "to a different journal", which often means "moving from more selective to less selective journals" [V]. Even after a decline, "the suggestions of the referees are usually relayed to the authors" [V]. — [Tao, Submit to an appropriate journal](https://terrytao.wordpress.com/advice-on-writing-papers/submit-to-an-appropriate-journal/)
- IOP policy: "we will not normally reconsider an article for our primary research journals if it has already been rejected in the same or a substantially similar form, without the option to resubmit, by this or any other IOP Publishing journal." Also: "If a submission has previously been rejected by one of our journals, please state this in your covering letter and clearly detail the revisions you have made" [S]. — [IOP Publishing Support](https://publishingsupport.iopscience.iop.org/?p=2603); [IOP decision types](https://publishingsupport.iopscience.iop.org/questions/decision-types-on-journal-articles/)
- IOP's transfer service lets the editor offer to move the paper to another IOP journal. If you accept, "the article, along with all relevant submission information and reviewer reports (if present), will be transferred" [S]. — [IOP article transfer service](https://publishingsupport.iopscience.iop.org/questions/article-transfer-service/)
- IOP "Reject to resubmit" decision type [S, title only]. — [IOP](https://publishingsupport.iopscience.iop.org/?p=1492)
- Editors' views from a MEPS theme section: editors do not object to resubmission elsewhere, "but all object to authors resubmitting a rejected ms practically unchanged to another journal". Many authors "never inform the new journal" of the prior rejection [S]. — [MEPS v258 p297-309](https://int-res.com/abstracts/meps/v258/p297-309)
- Pak: "You are never really done" and "Rewrite and republish" (§§6.1, 6.3); arXiv versions can be updated [V, headings]. — [Pak](https://www.math.ucla.edu/~pak/papers/how-to-write1.pdf)

### Inferences
- Practical protocol, synthesised from the above:
  1. Sort each referee comment into one of four bins: error or gap (must fix), clarity (fix, since it will recur), scope or interest (shapes re-targeting and framing), or preference (optional).
  2. Fix every correctness or clarity point even though the paper was rejected.
  3. If the objection was "not of interest to physicists", either strengthen the physical payoff for a similar journal or move to a mathematical-physics or probability journal.
  4. If the new journal is at a different publisher, there is generally no obligation to mention the previous rejection. The new journal may draw overlapping referees from a small community, though, so an unchanged paper risks the same report. Optionally offer the prior reports together with a response. Some editors value this, but it is a judgment call and I found no source stating a rule.
  5. Within IOP (for example JSTAT → J. Phys. A), disclosure in the cover letter is required.
  6. Cover letter: state the main result in one or two sentences, why it fits the journal's scope and readership, any prior-rejection disclosure with a summary of revisions where applicable, and suggested or excluded referees if the journal allows.

### Gaps
- Nature/Science careers pieces on rejection, and APS policies on prior rejection, were not fetched. Whether APS journals require disclosure of rejections elsewhere is unknown (APS does let authors transfer within its journal family, with reports [UNVERIFIED, memory]).

---

## (Brief) AI assistance: use and disclosure

### Takeaway
Publishers align with COPE: AI cannot be an author, authors bear full responsibility, and material use must be disclosed. IOP, JSTAT's publisher, requires a separate AI disclosure statement in the Acknowledgements when AI use materially contributes. Routine language editing does not need a separate statement.

### Cited Findings
- IOP: where AI use materially contributes, "authors must disclose this in a separate AI disclosure statement as part of the" Acknowledgement section. The statement should "identify the tool or model used, describe how it was used" and explain how outputs were checked. AI used in the research process itself should also be described in Methods. For routine spelling, grammar and language editing, "a separate disclosure statement is not required" [V]. — [IOP, Generative AI tools](https://publishingsupport.iopscience.iop.org/questions/generative-ai-tools/)
- IOP: "All authors remain fully responsible for the accuracy, originality and integrity of all content in their submission." Non-existent (hallucinated) references "will usually result in a rejection ... and potentially further sanctions", with retraction possible after publication. Hidden prompts aimed at peer review lead to "immediate rejection" [V]. — [IOP, Generative AI tools](https://publishingsupport.iopscience.iop.org/questions/generative-ai-tools/)
- AMS: amended its "Ethical Guidelines and Journal Policies" to adopt the COPE statement (Feb 2023): AI tools cannot be authors, and use must be disclosed. A 2023 paper called this a "stop-gap" and mentions an AMS "Advisory Group on Artificial Intelligence and the Mathematical Community" (July 2023) [S]. — [arXiv:2311.06981](https://arxiv.org/pdf/2311.06981)

### Inferences
- For a JSTAT submission, if AI materially helped with proofs, computations, literature search or drafting, include an Acknowledgements-section AI disclosure naming the tool, its role and how the output was verified. Verify every reference exists.

### Gaps
- I did not read the current AMS ethical guidelines page directly, and I did not find later AMS advisory-group output.
