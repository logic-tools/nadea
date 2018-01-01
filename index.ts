// NaDeA - License, source code and further information at https://logic-tools.github.io/
//
/// <reference path="references.d.ts"/>

// Update version number on page
var versionNumber = "0.9.9";
$(document).ready(() => setTitle());

// Set up index.nadea location
var isNadeaOnline = true;
var indexNadeaURL = isNadeaOnline ? "https://nadea.compute.dtu.dk/index.nadea" : "";
var readNadeaFileLocally = window.location.protocol === "file:";
var nadeaQuot = "''";

var INITIAL_PROOF = "OK{.}[]";
var isabelleFileFormatted = "";
var naturalDeductionAssistantThy = "";

// Unknown interface stores information about
// the unknowns in an uncompleted proof
interface Unknown {
    x: any;
    parent?: { x: Inductive, nq: number };
    inFm?: number;
    inAssumption?: number;
    inTm?: number;
    linkedTo?: Unknown[];
};

class State {
    p: Inductive;
    xs: Unknown[];
    gc: number;
};

var currentState: State;
var stateStack: IbStack;

var undefInductivesWithoutUnknowns: { parent: Inductive; self: Inductive; premiseIndex: number }[];

$(document).ready(() => {
    /*
     * Initialize a generic proof structure
     * - is to be changed to the correct ind. syn type when goal is completed, and a rule is chosen
     */
    initNewProof();

    /* jQuery event handlers */
    attachEventHandlersUnknowns();
    attachClickEvents();
    attachHashEventListeners();
    attachKeyBindings();

    // Load examples
    loadOnlineContents();

    // Update
    update(indexNadeaURL.length > 0 && window.location.hash.length > 0);
});

function setTitle(append: string = null) {
    var titleString = "NaDeA " + versionNumber + (append !== null ? " " + append : "");

    if (window.location.hash) {
        // Remove leading #
        var hashValue = window.location.hash.substring(1);

        // Match against number value
        var match = hashValue.search(/^([0-9]+)$/) !== -1;

        // No match
        if (match) {
            var proofID = "Hint " + hashValue;

            if (proofCodes[proofID] !== undefined)
                titleString += " #" + hashValue;
        }
    }

    $("title").html(titleString);
}

function initNewProof() {
    currentState = new State;
    currentState.p = new Inductive(null, []);
    currentState.xs = [{ x: currentState.p, inFm: 1 }];
    currentState.gc = 0;

    stateStack = new IbStack(currentState);
}

function loadProof(x: Inductive[], reverse = false) {
    var states = [];
    x.forEach(ind => {
        var s = new State();
        s.gc = getNumGeneratedConstants(ind);
        s.p = ind;
        s.xs = reconstructUnknownsFromProof(ind);

        if (reverse)
            states.unshift(s);
        else
            states.push(s);
    });

    // Set x as reference proof
    currentState = states[0];

    var s = states.pop();
    stateStack.reset(s);

    while (states.length > 0) {
        s = states.pop();
        stateStack.update(IbStackEvent.UPDATE_INTERNAL, s);
    }

    // Update the view
    update();
};


function update(hidden: boolean = false) {
    // Find premises that have goals without unknowns
    undefInductivesWithoutUnknowns = [];

    findUndefInductivesWithoutUnknowns(undefInductivesWithoutUnknowns, currentState.p, null, 0, 0);

    undefInductivesWithoutUnknowns.some((v, i) => {
        if (v.parent instanceof synExiE) {
            if ((<synExiE>v.parent).waitingForPCompletion) {
                (<synExiE>v.parent).waitingForPCompletion = false;
                (<synExiE>v.parent).getNewsAndSub(getNewConstant(currentState.p));

                pushIndices(undefInductivesWithoutUnknowns, i + 1, 1);
                undefInductivesWithoutUnknowns[i + 1] = { parent: v.parent, self: v.self, premiseIndex: 1 };

                return true;
            }
        }

        return false;
    });

    // Check if "Assume" rule can be applied to found premises
    undefInductivesWithoutUnknowns.forEach(v => {
        if (v.self.premises.length === 0)
            if (v.self.trueByAssumption !== true)
                v.self.checkGoal();
    });

    updateHeader();
    updateFrame(hidden);

    updateProofLineStatus();
}

function updateHeader() {
    // Retrieve data
    var numUnknowns: number = countUnknowns(currentState.p) + currentState.p.waiting();
    var stateStackSize: number = stateStack.stack.length;
    var stateStackMark: number = stateStack.markedIndex === null ? stateStackSize : stateStack.markedIndex + 1;

    // Infer actions
    var disableUndo: boolean = stateStackMark < 2;
    var disableStop: boolean = stateStackMark === stateStackSize;

    var finished = numUnknowns === 0;

    // Prepare iceberg info string
    var ibGoals: string = (numUnknowns > 99 ? "**" : finished ? "&#9786" : numUnknowns.toString());
    var ibInfo: string = (stateStackMark > 9999 ? "****" : stateStackMark) + "/" + (stateStackSize > 9999 ? "****" : stateStackSize);

    // Update header
    var proofGoals = $("#header #rightbar .proofGoals");
    proofGoals.html(ibGoals);

    $("#header #rightbar .proofInfo").html(ibInfo);

    var undoBtn = $("#header #rightbar .undo");
    var stopBtn = $("#header #rightbar .stop");

    // Disable undo
    if (disableUndo) {
        undoBtn.addClass("disabled");
    } else {
        undoBtn.removeClass("disabled");
    }

    // Disable stop
    if (disableStop) {
        stopBtn.addClass("disabled");
    } else {
        stopBtn.removeClass("disabled");
    }
}

function updateFrame(hidden: boolean) {
    // Clear the frame
    $("#frame #frameContainer").children().remove();

    if (hidden)
        $("#frame #frameContainer").hide();
    else
        $("#frame #frameContainer").show();

    // Write proof lines
    appendLines(currentState.p, 0);

    // Update indices on HTML elements to reflect keys in array of unknowns
    updateExistingIndexUnknowns();

    $(".indentProof").each((i, v) => {
        $(v).css({ paddingLeft: (1.3 * zoomCoefficient * (+$(v).data("indent"))).toFixed(2) + "vw" });
    });
}


// Dict to proof codes stored
var proofCodes: { [id: string]: string } = {};

function loadOnlineContents() {
    /* Tests and hints */

    // Initially the tests are the initial proof state
    proofCodes = {};

    proofCodes["Test 0"] = ". This is the initial proof state with no formula and it can be used as a starting point for proofs - try proving the formula A by applying the so-called Boole rule... :-)\n" + INITIAL_PROOF + "\n";

    for (var i = 1; i <= 9; i++)
        proofCodes["Test " + i] = "";

    proofCodes["Proof index"] = ". The proof index collects the final proof state for all tests but no tests was provided.\n";


    if (indexNadeaURL == "") {
        var nadeaContents = ". Ignored line...\n" +
            "# Test 0\n" +
            proofCodes["Test 0"] +
            "# Hint 0\n" +
            "\n" +
            ". Turn on edit mode and build the formula using Implication and the predicate A with no arguments.\n" +
            "...\n" +
            ". After building the formula, apply the rule Imp_I (Implication-Introduction) to prove the formula A by assumption of A.\n" +
            "ImpI{Imp{Pre{A}{}}{Pre{A}{}}}[]:{OK{Pre{A}{}}[Pre{A}{}]}\n" +
            "OK{Imp{Pre{A}{}}{Pre{A}{}}}[]\n" +
            "OK{Imp{Pre{A}{}}{Pre{.}{}}}[]\n" +
            "OK{Imp{Pre{.}{}}{Pre{.}{}}}[]\n" +
            "OK{Imp{Pre{.}{}}{Pre{.}{.}}}[]\n" +
            "OK{Imp{Pre{.}{.}}{Pre{.}{.}}}[]\n" +
            "OK{Imp{Pre{.}{.}}{.}}[]\n" +
            "OK{Imp{.}{.}}[]\n" +
            "OK{.}[]";

        readNadeaTestData(nadeaContents);
    }

    var xhr = new XMLHttpRequest();
    xhr.overrideMimeType("text/plain");

    if (readNadeaFileLocally) {
        // Try to fetch from server file system

        xhr.onreadystatechange = () => {
            if (xhr.readyState == 4 && xhr.status === 200) {
                readNadeaTestData(xhr.responseText);
            }
        }

        xhr.ontimeout = () => {
            readNadeaFileLocally = false;
            loadOnlineContents();
        }

        xhr.open("GET", "index.nadea", true);
        xhr.timeout = 5000;
        xhr.setRequestHeader('Content-type', 'text/plain; charset=utf-8');
        xhr.send(null);
    }

    else {
        // Load file from the net if not yet loaded
        xhr.onreadystatechange = () => {
            if (xhr.readyState == 4 && xhr.status === 200) {
                readNadeaTestData(xhr.responseText);
            }
        }

        xhr.ontimeout = () => {
            console.log("Failed to load tests and hints.");
        }

        xhr.open("GET", indexNadeaURL, true);
        xhr.timeout = 5000;
        xhr.setRequestHeader('Content-type', 'text/plain; charset=utf-8');
        xhr.send(null);
    }

    /* Isabelle NaDeA file */
    var xhr2 = new XMLHttpRequest();
    xhr2.overrideMimeType("text/plain");

    if (readNadeaFileLocally) {
        // Try to fetch from server file system

        xhr2.onreadystatechange = () => {
            if (xhr2.readyState == 4 && xhr2.status === 200) {
                readNadeaIsabelleFile(xhr2.responseText);
            }
        }

        xhr2.ontimeout = () => {
            readNadeaFileLocally = false;
            loadOnlineContents();
        }

        xhr2.open("GET", "NaDeA.thy", true);
        xhr2.timeout = 5000;
        xhr2.setRequestHeader('Content-type', 'text/plain; charset=utf-8');
        xhr2.send(null);
    }

    else {
        // Load file from the net if not yet loaded
        xhr2.onreadystatechange = () => {
            if (xhr2.readyState == 4 && xhr2.status === 200) {
                readNadeaIsabelleFile(xhr2.responseText);
            }
        }

        xhr2.ontimeout = () => {
            console.log("Failed to load isabelle file.");
        }

        xhr2.open("GET", indexNadeaURL.replace("index.nadea", "NaDeA.thy"), true);
        xhr2.timeout = 5000;
        xhr2.setRequestHeader('Content-type', 'text/plain; charset=iso-utf-8');
        xhr2.send(null);
    }

    /* Isabelle Natural_Deduction_Assistant file */
    var xhr3 = new XMLHttpRequest();
    xhr3.overrideMimeType("text/plain");

    if (readNadeaFileLocally) {
        // Try to fetch from server file system

        xhr3.onreadystatechange = () => {
            if (xhr3.readyState == 4 && xhr3.status === 200) {
                naturalDeductionAssistantThy = xhr3.responseText;
            }
        }

        xhr3.ontimeout = () => {
            readNadeaFileLocally = false;
        }

        xhr3.open("GET", "Natural_Deduction_Assistant.thy", true);
        xhr3.timeout = 5000;
        xhr3.setRequestHeader('Content-type', 'text/plain; charset=utf-8');
        xhr3.send(null);
    } else {
        // Load file from the net if not yet loaded
        xhr3.onreadystatechange = () => {
            if (xhr3.readyState == 4 && xhr3.status === 200) {
                naturalDeductionAssistantThy = xhr3.responseText;
            }
        }

        xhr3.ontimeout = () => {
            console.log("Failed to load isabelle assistant file.");
        }

        xhr3.open("GET", indexNadeaURL.replace("index.nadea", "Natural_Deduction_Assistant.thy"), true);
        xhr3.timeout = 5000;
        xhr3.setRequestHeader('Content-type', 'text/plain; charset=iso-utf-8');
        xhr3.send(null);
    }
}

function readNadeaTestData(rawFileText: string) {
    // Go through each line of the loaded .nadea file

    var currentProofID: string = null;
    var currentProofCode: string = null;
    var proofIndexData: { key: string, value: string }[] = [];

    var endOfComments: boolean = null;

    var lines = rawFileText.split(/\n/).filter(x => { return x.trim() !== "" });

    var addProofCode = (id, code, bypassCheck = false) => {
        if (id !== null) {
            // End of proof code
            if (bypassCheck || isValidProofCode(currentProofCode))
                proofCodes[id] = code;
            else
                console.log("Invalid proof code (" + id + ") read from '.nadea' file:\n" + code);
        }
    };

    lines.forEach((x, i) => {
        // Check if recognized as valid proof ID
        var idMatch = x.match(/^\#\s*((Test\s+([0-9]+|suite))|(Hint\s+[0-9]+))\s*$/);

        if (idMatch !== null) {
            addProofCode(currentProofID, currentProofCode);

            // Initialize new proof
            currentProofID = idMatch[1];
            currentProofCode = "";
            endOfComments = false;

        } else if (currentProofID !== null) {
            // Check if line is a comment
            var isComment: boolean = x.search(/^\./) !== -1;

            // If the comment block is exceeded, ignore additional comment lines
            // Used to filter away some empty comment lines after proof code
            if (!endOfComments && !isComment) {
                endOfComments = true;

                var idMatch2 = currentProofID.match(/((Test)|(Hint)) ([0-9]+)/);

                if (idMatch2 !== null) {
                    proofIndexData.push({ key: idMatch2[0], value: x });
                }
            }

            if (endOfComments && isComment)
                return;

            // Append line to current proof code
            currentProofCode += x + "\n";
        }
    });

    var regex = /((Test)|(Hint)) ([0-9]+)/;
    proofIndexData.sort((x, y) => {
        var xm = regex.exec(x.key);
        var ym = regex.exec(y.key);

        if (xm[1] == "Test" && ym[1] == "Hint")
            return -1;
        else if (ym[1] == "Test" && xm[1] == "Hint")
            return 1;

        if (+ym[4] > +xm[4])
            return -1;
        else if (+xm[4] > +ym[4])
            return 1;

        return 0;
    });

    var proofIndexCodes = proofIndexData.map((x, i) => {
        return x.value;
    });

    addProofCode(currentProofID, currentProofCode);

    if (proofIndexData.length > 0)
        addProofCode("Proof index", ". The proof index collects the final proof state for all tests and hints.\n\n" + proofIndexCodes.join("\n") + "\n\n. Load and click the Undo button to show the proof states.\n");

    var allProofCodes = ". NaDeA index file: \"" + indexNadeaURL + "\"\n\n";

    for (var key in proofCodes) {
        if (key != "Proof index" && proofCodes[key].length > 0)
            allProofCodes += "# " + key + "\n\n" + proofCodes[key] + "\n";
    }

    allProofCodes += ". More tests and hints are available online.\n";

    addProofCode("All proofs", allProofCodes, true);

    // Wait for nadea-file
    $(window).trigger("hashchange");

    // Update exercise page
    setupExerciseAndHintData();
}

var isabelleKeyWords: { keyword: string, description: string }[] = [
    {
        keyword: "theory",
        description: "Defines a theory."
    },
    {
        keyword: "imports",
        description: "Imports a theory to be used in the current theory."
    },
    {
        keyword: "begin",
        description: "Marks the beginning of the theory content."
    },
    {
        keyword: "type_synonym",
        description: "Introduces a type synonym, just an abbreviation, for an existing type."
    },
    {
        keyword: "datatype",
        description: "Defines a datatype within the theory."
    },
    {
        keyword: "primrec",
        description: "Defines a primitive recursive function."
    },
    {
        keyword: "and",
        description: "Used in the syntax to gather multiple definitions etc."
    },
    {
        keyword: "where",
        description: "Used in certain declarations."
    },
    {
        keyword: "inductive",
        description: "Defines an inductive definition."
    },
    {
        keyword: "lemma",
        description: "States a lemma (similar to a theorem) in the theory and is followed by a proof."
    },
    {
        keyword: "proof",
        description: "Marks the beginning of a proof block."
    },
    {
        keyword: "have",
        description: "States a result in a proof block and is followed by a proof."
    },
    {
        keyword: "qed",
        description: "Marks the end a proof block."
    },
    {
        keyword: "then",
        description: "Uses the previous result to prove the following."
    },
    {
        keyword: "show",
        description: "States the final result of a proof block."
    },
    {
        keyword: "fun",
        description: "Defines a new function declaration inside the theory."
    },
    {
        keyword: "fix",
        description: "Defines a local arbitrary constant in the proof."
    },
    {
        keyword: "assume",
        description: "States an assumption to be used."
    },
    {
        keyword: "also",
        description: "Collects in a transitive chain the previous result in the proof"
    },
    {
        keyword: "using",
        description: "Uses the given results to prove a result."
    },
    {
        keyword: "finally",
        description: "Uses the collected results in a transitive chain to prove a result."
    },
    {
        keyword: "next",
        description: "Marks the start of a case inside the proof block."
    },
    {
        keyword: "obtain",
        description: "States the properties of a constant and gives it a name."
    },
    {
        keyword: "moreover",
        description: "Collects the previous result in the proof."
    },
    {
        keyword: "ultimately",
        description: "Uses the collected results to prove a result."
    },
    {
        keyword: "theorem",
        description: "States a theorem in the theory and is followed by a proof."
    },
    {
        keyword: "end",
        description: "Marks the end of the current theory."
    },
    {
        keyword: "oops",
        description: "Placeholder for a missing proof."
    },
    {
        keyword: "proposition",
        description: "States a proposition (similar to a theorem) in the theory and is followed by a proof."
    },
    {
        keyword: "corollary",
        description: "States a corollary (similar to a theorem) in the theory and is followed by a proof."
    },
    {
        keyword: "for",
        description: "Defines a local parameter."
    },
    {
        keyword: "by",
        description: "Finishes a proof given one or two proof methods."
    },
    {
        keyword: "abbreviation",
        description: "Introduces a syntactic abbreviation."
    },
    {
        keyword: "case",
        description: "Declares the case proven next."
    },
    {
        keyword: "text",
        description: "Introduces an exported comment in plain text."
    },
    {
        keyword: "section",
        description: "Introduces a section given a title."
    },
    {
        keyword: "subsection",
        description: "Introduces a subsection given a title."
    },
    {
        keyword: "definition",
        description: "Hides an expression behind a name."
    },
    {
        keyword: "with",
        description: "Uses the given results to prove a result."
    },
    {
        keyword: "unfolding",
        description: "Unfolds a definition revealing the expression inside."
    },
    {
        keyword: "let",
        description: "Introduces a local abbreviation."
    },
    {
        keyword: "apply",
        description: "Modifies the goal by applying the given rule."
    },
    {
        keyword: "done",
        description: "Marks the end of an apply-proof block."
    },
    {
        keyword: "declare",
        description: "Attaches attributes to an earlier declaration."
    },
];

isabelleKeyWords.sort((x, y) => {
    return x.keyword.localeCompare(y.keyword);
});

function formatIsabelle(rawTextFile: string): string[] {
    // Keywords in bold
    var isabelleFileLines = rawTextFile.split(/(?:\r\n|\r|\n)/);

    var regexStr = "(";
    isabelleKeyWords.forEach((obj, i) => {
        var k = obj.keyword;
        regexStr += "(\\s(" + k + ")\\s)|(\\s(" + k + "))|((" + k + "\\s))|(^(" + k + ")$)";

        if (i !== isabelleKeyWords.length - 1)
            regexStr += "|";
    });
    regexStr += ")";

    var regex = new RegExp(regexStr, "g");
    var isabelleFileLinesFormatted: string[] = [];

    isabelleFileLines.forEach((l, i) => {
        // Check for strings: "", (* *), \<open> \<close>
        // Assumes they are not nested.

        isabelleFileLinesFormatted[i] = l;

        var stringIndices: { s: number, e: number }[] = [];

        var inString = false;
        var stringStart: number = null;

        for (var j = 0; j < isabelleFileLines[i].length; j++) {
            var c = isabelleFileLines[i].charAt(j);

            if (c == '"') {
                inString = !inString;

                if (inString) {
                    stringStart = j;
                } else {
                    stringIndices.push({ s: stringStart, e: j });
                }
            }
        }

        var m: string[] = isabelleFileLines[i].match(regex);

        if (m !== null) {
            var startIndex = 0;

            m.forEach((v, j) => {
                var replaceIndex = isabelleFileLines[i].indexOf(v, startIndex);

                var inString = false;
                stringIndices.forEach(x => {
                    if (replaceIndex >= x.s && replaceIndex < x.e) {
                        inString = true;
                    }
                });

                if (!inString) {
                    var replace = m[j].replace(/(\s?)([^\s]*)(\s?)/, "$1<strong>$2</strong>$3");
                    isabelleFileLinesFormatted[i] = isabelleFileLinesFormatted[i].replace(m[j], replace);
                }

                startIndex = replaceIndex + 1;
            });
        }
    });

    return isabelleFileLinesFormatted;
}

function readNadeaIsabelleFile(rawTextFile: string) {
    // Keywords in bold
    var rawTextFileLines = rawTextFile.split(/(?:\r\n|\r|\n)/);

    var isabelleFileLines: string[][] = [];
    rawTextFileLines.forEach((l, i) => {
        var split = l.match(/(.*)\s+\(\*(.*)\*\)/);

        if (split === null)
            return true;

        isabelleFileLines[i] = [split[1], split[2]];
    });


    var regexStr = "(";
    isabelleKeyWords.forEach((obj, i) => {
        var k = obj.keyword;
        regexStr += "(\\s(" + k + ")\\s)|(\\s(" + k + "))|((" + k + "\\s))";

        if (i !== isabelleKeyWords.length - 1)
            regexStr += "|";
    });
    regexStr += ")";
    var regex = new RegExp(regexStr, "g");

    var isabelleFileLinesFormatted: string[] = [];

    isabelleFileLines.forEach((l, i) => {
        // Check for strings: ""

        isabelleFileLinesFormatted[i] = l[0];

        var stringIndices: { s: number, e: number }[] = [];

        var inString = false;
        var stringStart: number = null;

        for (var j = 0; j < isabelleFileLines[i][0].length; j++) {
            var c = isabelleFileLines[i][0].charAt(j);

            if (c == '"') {
                inString = !inString;

                if (inString) {
                    stringStart = j;
                } else {
                    stringIndices.push({ s: stringStart, e: j });
                }
            }
        }

        var m: string[] = isabelleFileLines[i][0].match(regex);

        if (m !== null) {
            var startIndex = 0;

            m.forEach((v, j) => {
                var replaceIndex = isabelleFileLines[i][0].indexOf(v, startIndex);

                var inString = false;
                stringIndices.forEach(x => {
                    if (replaceIndex >= x.s && replaceIndex < x.e) {
                        inString = true;
                    }
                });

                if (!inString) {
                    var replace = m[j].replace(/(\s?)([^\s]*)(\s?)/, "$1<strong>$2</strong>$3");
                    isabelleFileLinesFormatted[i] = isabelleFileLinesFormatted[i].replace(m[j], replace);
                }

                startIndex = replaceIndex + 1;
            });
        }
    });

    isabelleFileFormatted = "";

    isabelleFileLines.forEach((l, i) => {
        var left = isabelleFileLinesFormatted[i] === undefined ? l[0] : isabelleFileLinesFormatted[i];
        isabelleFileFormatted += left + " (*" + l[1] + "*)\n";
    });
}

var zoomCoefficient = 1;
$(document).ready(() => {
    // Get width of window element
    var vw = $(window).width();

    // Turn values from jQuery CSS (in pixels) into vw units
    var frameFontSize = +(+$("#frame").css("font-size").replace("px", "")).toFixed(2) / vw * 100;
    var proofLineHeight = +(+$(".line > *").css("line-height").replace("px", "")).toFixed(2) / vw * 100;

    $(window).resize(() => {
        // (Re-)align proof container with header
        $("#container").css({ marginTop: $("#headerContainer").height() + "px" });

        // Get an approximate value of the zoom level
        var zoomCoefficientPrevious = zoomCoefficient;
        zoomCoefficient = (vw / $(window).width());

        if (zoomCoefficient != zoomCoefficientPrevious) {
            // Set relevant css in vw units
            $("#frame, .loadTextarea").css({ fontSize: (frameFontSize * zoomCoefficient).toFixed(2) + "vw" });
            $(".line > *").css({ lineHeight: (proofLineHeight * zoomCoefficient).toFixed(2) + "vw" });

            $(".indentProof").each((i, v) => {
                $(v).css({ paddingLeft: (1.3 * zoomCoefficient * (+$(v).data("indent"))).toFixed(2) + "vw" });
            });
        }
    });

    // Invoke resize function on each page load
    $(window).resize();
});

function attachEventHandlersUnknowns() {
    // Add click functions to unknowns in proof

    var indexUnknown: number;

    /*
     * New syn rule click handler
     */
    $(document).on("click", "a.newSynRule", e => {
        // Get clicked inductive
        var parentInductive = undefInductivesWithoutUnknowns[+$(e.currentTarget).data("synUnknownIndex")];
        var x: Inductive;

        if (parentInductive.parent === null)
            x = currentState.p;
        else
            x = parentInductive.parent.premises[parentInductive.premiseIndex];

        newOverlay(e, "newSynRule", (x: Inductive) => {

            prepareCurrentStateUpdate();

            // Get parent inductive in order to replace generic "inductive" structure with correct structure for the selected rule
            if (parentInductive.parent === null)
                currentState.p = x;
            else
                parentInductive.parent.premises[parentInductive.premiseIndex] = x;

            // Special procedures for generating premises for Uni_E and Uni_I
            if (x instanceof synUniI)
                x.getPremises(getNewConstant(currentState.p));

            else if (x instanceof synUniE) {
                termHandlerUniE(e, x);
            }

            else
                x.getPremises(null, null);


            // Go through each line in order to compute the correct index to insert the unknown premise at
            var insertIndex = 0;

            $(".line").each((i, line) => {
                insertIndex += $(line).find("a").not(".newSynRule").length;

                if ($(line).find("a.newSynRule").is(e.currentTarget)) {
                    return false;
                }
            });

            // Add generated unknowns
            addUnknownsPremises(x, insertIndex);

            // Update the view
            update();
        }, x);
    });

    /*
     * New formula
     */

    $(document).on("click", "a.newFormula", e => {
        // Get index of unknown that is to be replaced
        indexUnknown = +$(e.currentTarget).data("indexUnknown");

        newOverlay(e, "newFormula", (fm: Formula) => {
            prepareCurrentStateUpdate();

            var replacedUnknowns = replaceUnknownsFormula(currentState.xs[indexUnknown], fm);

            // Remove previous unknowns from the pool of unknowns
            var linkedUnks: Unknown[][] = [[], []];

            replacedUnknowns.forEach(v => {
                currentState.xs.some((w, removeIndex) => {
                    if (v === w) {
                        var unk1: Unknown,
                            unk2: Unknown;

                        // Unknown is replaced with a one argument formula
                        // Insert new unknown formula
                        if (fm instanceof FormulaOneArg) {
                            unk1 = { x: fm, inFm: 1 };

                            currentState.xs[removeIndex] = unk1;

                            linkedUnks[0].push(unk1);
                        }

                        // Unknown is replaced with a two argument formula
                        // Insert two new unknown formulas
                        else if (fm instanceof FormulaTwoArg || fm instanceof fmPre) {
                            pushIndices(currentState.xs, removeIndex + 1, 1);

                            unk1 = { x: fm, inFm: 1 };
                            unk2 = { x: fm, inFm: 2 };

                            currentState.xs[removeIndex] = unk1;
                            currentState.xs[removeIndex + 1] = unk2;

                            linkedUnks[0].push(unk1);
                            linkedUnks[1].push(unk2);
                        }

                        else if (fm instanceof fmFalsity) {
                            currentState.xs.splice(removeIndex, 1);
                        }

                        return true;
                    }
                });
            });

            // Set (eventual) links between unknowns
            setLinkedUnks(linkedUnks);

            // Update the view
            update();
        });
    });

    /*
     * New ID
     */

    $(document).on("click", "a.newID", e => {
        // Index of unknown to be replaced
        indexUnknown = +$(e.currentTarget).data("indexUnknown");

        newOverlay(e, "newID", (id: string) => {

            prepareCurrentStateUpdate();

            var replacedUnknowns = replaceUnknownsID(currentState.xs[indexUnknown], id);

            replacedUnknowns.forEach(v => {
                currentState.xs.some((w, removeIndex) => {
                    if (v === w) {
                        currentState.xs.splice(removeIndex, 1);

                        return true;
                    }
                });
            });

            // Update the view
            update();
        }, $(e.currentTarget).hasClass("pre"));
    });

    /*
     * New Terms
     */

    function tmCallback(indexUnknown: number, tms: number[]) {
        prepareCurrentStateUpdate();

        var replacedUnknowns = replaceUnknownsTm(currentState.xs[indexUnknown], tms);

        // Remove previous unknowns from the pool of unknowns
        var linkedUnks: Unknown[][] = [];
        var skip: Unknown[] = [];

        replacedUnknowns.forEach(v => {
            currentState.xs.some((w, removeIndex) => {
                // Find array index of each replaced unknown
                if (v === w) {

                    if (currentState.xs[removeIndex].x instanceof fmPre
                        || currentState.xs[removeIndex].x instanceof tmFun) {

                        if (currentState.xs[removeIndex].inFm == 1)
                            return false;

                        var newTmFuns: tmFun[] = [];

                        if (currentState.xs[removeIndex].x instanceof fmPre)
                            (<fmPre>currentState.xs[removeIndex].x).tms.forEach((u, i) => {
                                if (u instanceof tmFun)
                                    if (u.id === null && u.tms === null)
                                        if (v.inTm === undefined || v.inTm === i)
                                            newTmFuns.push(<tmFun>u);
                            });

                        else if (currentState.xs[removeIndex].x instanceof tmFun)
                            (<tmFun>currentState.xs[removeIndex].x).tms.forEach((u, i) => {
                                if (u instanceof tmFun)
                                    if (u.id === null && u.tms === null)
                                        if (v.inTm === undefined || v.inTm === i)
                                            newTmFuns.push(<tmFun>u);
                            });

                        currentState.xs.splice(removeIndex, 1);

                        if (newTmFuns.length > 0) {
                            pushIndices(currentState.xs, removeIndex, newTmFuns.length * 2);

                            for (var i = 0; i < newTmFuns.length; i++) {
                                var tm = newTmFuns[i];

                                var unk1 = { x: tm, inFm: 1 };
                                var unk2 = { x: tm, inFm: 2 };

                                if (linkedUnks[i * 2] === undefined)
                                    linkedUnks[i * 2] = [];

                                if (linkedUnks[i * 2 + 1] === undefined)
                                    linkedUnks[i * 2 + 1] = [];

                                linkedUnks[i * 2].push(unk1);
                                linkedUnks[i * 2 + 1].push(unk2);
                                currentState.xs[i * 2 + removeIndex] = unk1;
                                currentState.xs[i * 2 + 1 + removeIndex] = unk2;
                            }

                        }
                    }

                    else {
                        console.log(currentState.xs[removeIndex]);
                        throw new Error("Expecting unknown term list, that is to be replaced");
                    }

                    return true;
                }
            });
        });

        // Set links between unknowns
        setLinkedUnks(linkedUnks);

        // Update the view
        update();
    }

    // Attach click handlers with previously defined callback functions
    $(document).on("click", "a.newTms", (e) => {

        indexUnknown = +$(e.currentTarget).data("indexUnknown");

        newOverlay(e, "newTms", tmCallback, indexUnknown);
    });

    $(document).on("click", "a.newTm", (e) => {

        indexUnknown = +$(e.currentTarget).data("indexUnknown");

        newOverlay(e, "newTm", tmCallback, indexUnknown);
    });

    $(document).on("click", "a.selectTerms", e => {
        indexUnknown = +$(e.currentTarget).data("indexUnknown");

        var parentInductive = undefInductivesWithoutUnknowns[+$(e.currentTarget).data("synUnknownIndex")];
        var x: Inductive;

        if (parentInductive.parent === null)
            x = currentState.p;
        else
            x = parentInductive.parent.premises[parentInductive.premiseIndex];

        termHandlerUniE(e, x);
    });
}


function addUnknownsPremises(x, insertIndex: number): void {
    // Generate unknowns in premises based on selected rule
    // Rules listed just below have no new unknowns
    if (x instanceof synBool
        || x instanceof synImpI
        || x instanceof synDisI1
        || x instanceof synDisI2
        || x instanceof synConI
        || x instanceof synUniE
        || x instanceof synUniI)
        return;
    else if (x instanceof synImpE) {
        pushIndices(currentState.xs, insertIndex, 2);

        var unk1: Unknown = { x: (<synImpE>x).premises[0].goal, inFm: 1 };
        var unk2: Unknown = { x: (<synImpE>x).premises[1], inFm: 1, linkedTo: [unk1] };
        unk1.linkedTo = [unk2];

        currentState.xs[insertIndex] = unk1;
        currentState.xs[insertIndex + 1] = unk2;
    }

    else if (x instanceof synDisE) {
        pushIndices(currentState.xs, insertIndex, 4);

        var unk1: Unknown = { x: (<synDisE>x).premises[0].goal, inFm: 1 };
        var unk2: Unknown = { x: (<synDisE>x).premises[0].goal, inFm: 2 };
        var unk3: Unknown = { x: (<synDisE>x).premises[1], inAssumption: 0, linkedTo: [unk1] };
        var unk4: Unknown = { x: (<synDisE>x).premises[2], inAssumption: 0, linkedTo: [unk2] };

        unk1.linkedTo = [unk3];
        unk2.linkedTo = [unk4];

        currentState.xs[insertIndex] = unk1;
        currentState.xs[insertIndex + 1] = unk2;
        currentState.xs[insertIndex + 2] = unk3;
        currentState.xs[insertIndex + 3] = unk4;
    }

    else if (x instanceof synConE1) {
        pushIndices(currentState.xs, insertIndex, 1);
        currentState.xs[insertIndex] = { x: (<synConE1>x).premises[0].goal, inFm: 2 };
    }

    else if (x instanceof synConE2) {
        pushIndices(currentState.xs, insertIndex, 1);
        currentState.xs[insertIndex] = { x: (<synConE1>x).premises[0].goal, inFm: 1 };
    }

    else if (x instanceof synExiE) {
        pushIndices(currentState.xs, insertIndex, 1);
        currentState.xs[insertIndex] = { x: (<synConE1>x).premises[0].goal, inFm: 1 };
    }

    else if (x instanceof synExiI) {
        var getQuantifiedVarsAsUnknowns: (y: any, nq: number, p?: any, i?: number) => Unknown[] = (y, nq, p = null, i = 0) => {

            var r: Unknown[] = [];

            if (y instanceof fmUni || y instanceof fmExi) {
                r = getQuantifiedVarsAsUnknowns((<FormulaOneArg>y).fm, nq + 1, y);
            }


            else if (y instanceof FormulaOneArg) {
                r = getQuantifiedVarsAsUnknowns((<FormulaOneArg>y).fm, nq, y);
            }

            else if (y instanceof FormulaTwoArg) {
                r = getQuantifiedVarsAsUnknowns((<FormulaTwoArg>y).lhs, nq, y)
                    .concat(getQuantifiedVarsAsUnknowns((<FormulaTwoArg>y).rhs, nq, y));
            }

            else if (y instanceof fmPre) {
                (<fmPre>y).tms.forEach((e, j) => {
                    getQuantifiedVarsAsUnknowns(e, nq, y, j).forEach(e => { r.push(e) });
                });
            }

            else if (y instanceof tmFun) {
                (<tmFun>y).tms.forEach((e, j) => {
                    getQuantifiedVarsAsUnknowns(e, nq, y, j).forEach(e => r.push(e));
                });
            }

            else if (y === null && (p instanceof fmPre || p instanceof tmFun)) {
                var u: Unknown = {
                    x: p, inTm: i, parent: { x: x, nq: nq }
                };
                r.push(u);
            }

            else if (y instanceof Inductive) {
                r = getQuantifiedVarsAsUnknowns((<Inductive>y).goal, nq, y);

                r.forEach(e => {
                    e.linkedTo = r.filter(k => k !== e);
                });
            }

            return r;
        };

        var quantifiedTerms = getQuantifiedVarsAsUnknowns((<synExiI>x).premises[0], 0);

        pushIndices(currentState.xs, insertIndex, quantifiedTerms.length);

        quantifiedTerms.forEach((e, i) => {
            currentState.xs[insertIndex + i] = e;
        });
    }

    else {
        console.log(x);
        throw new Error("Unexpected type of object, x");
    }
}

function replaceUnknownsFormula(u: Unknown, fm: Formula, updateLinked: boolean = true): Unknown[] {
    // Replace previous unknown with new formula
    if (u.x instanceof FormulaOneArg) {
        (<FormulaOneArg>u.x).fm = fm;
    }

    // Replacer either LHS or RHS of two argument formula
    else if (u.x instanceof FormulaTwoArg) {
        if (u.inFm == 1)
            (<FormulaTwoArg>u.x).lhs = fm;
        else
            (<FormulaTwoArg>u.x).rhs = fm;
    }

    // Set goal of new inductive
    else if (u.x instanceof Inductive) {
        if (u.inFm === 1)
            (<Inductive>u.x).goal = fm;
        else if (u.inAssumption !== undefined)
            (<Inductive>u.x).assumptions[u.inAssumption] = fm;

    }

    else {
        console.log(u);
        throw new Error("Expecting inductive, one argument formula or two argument formula.");
    }

    var unknowns: Unknown[] = [u];

    // Update linked unknowns
    if (updateLinked && u.linkedTo !== undefined)
        u.linkedTo.forEach(v => {
            replaceUnknownsFormula(v, fm, false).forEach(w => {
                unknowns.push(w);
            });
        });

    return unknowns;
}

function replaceUnknownsID(u: Unknown, id: string, updateLinked: boolean = true): Unknown[] {

    // Replace id of predicate
    if (u.x instanceof fmPre && u.inFm == 1) {
        (<fmPre>u.x).id = id;
    }

    // Replace id of function term
    else if (u.x instanceof tmFun && u.inFm == 1) {
        (<tmFun>u.x).id = id;
    }

    else {
        console.log(u);
        throw new Error("Expecting unknown ID in predicate or function");
    }

    var unknowns: Unknown[] = [u];

    // Update linked unknowns
    if (updateLinked && u.linkedTo !== undefined)
        u.linkedTo.forEach(v => {
            replaceUnknownsID(v, id, false).forEach(w => {
                unknowns.push(w);
            });
        });

    return unknowns;
}

function replaceUnknownsTm(u: Unknown, tmNats: number[], updateLinked: boolean = true): Unknown[] {

    if (u.x instanceof fmPre || u.x instanceof tmFun) {
        if (u.inFm === 1)
            return;

        var unknownTms: Term[];

        if (u.x instanceof fmPre) {
            if (u.inFm == 2)
                // Entire list of terms is unknown. Initialize list.
                (<fmPre>u.x).tms = [];

            unknownTms = (<fmPre>u.x).tms;
        }

        else {
            if (u.inFm == 2)
                // Entire list of terms is unknown. Initialize list.
                (<tmFun>u.x).tms = [];

            unknownTms = (<tmFun>u.x).tms;
        }

        tmNats.forEach(v => {
            if (v === -1) {
                var tmF = new tmFun(null, null);

                if (u.inFm === 2)
                    unknownTms.push(tmF);
                else if (u.inTm !== undefined)
                    unknownTms[u.inTm] = tmF;
            }

            else {
                var tmV = new tmVar(v);

                if (u.inFm === 2)
                    unknownTms.push(tmV);
                else if (u.inTm !== undefined)
                    unknownTms[u.inTm] = tmV;
            }
        });
    }

    else {
        console.log(u);
        throw new Error("Expecting unknown term list, that is to be replaced");
    }

    var unknowns: Unknown[] = [u];

    // Update linked unknowns
    if (updateLinked && u.linkedTo !== undefined)
        u.linkedTo.forEach(v => {
            replaceUnknownsTm(v, tmNats, false).forEach(w => {
                unknowns.push(w);
            });
        });

    return unknowns;
}


function termHandlerUniE(e: JQueryEventObject, x: Inductive) {
    // New overlay that lets you choose existing term to quantify
    newOverlay(e, "existingTerm", (ts: { term: Term, occs?: number[] }[]) => {
        if (ts.length == 0)
            return;

        if (!(x instanceof synUniE))
            return;

        prepareCurrentStateUpdate();

        (<synUniE>x).waitingForTermSelection = false;

        x.getPremises.apply(x, ts);

        update();
    }, x);
}

//
// Html write
//

function appendLines(x: Inductive, n: number, i: number = 1, j: number = 0): [number, number] {
    var htmlString: string = "<div class=\"line\">";

    // Line numbering
    htmlString += '<div class="lineNumber">' + i + '</div>';

    // Left
    htmlString += '<div class="left code' + (!editModeOn ? ' hidden' : '') + '">';

    htmlString += '<div class="indentProof" data-indent="' + n + '">';

    htmlString += "<div class='synGoal'><div class='ok'>OK</div><div class='arg'>" + getInternalSyntaxHTML(x.goal) + "</div><div class='arg'><div class='leftBracket'>[</div>";

    // Assumptions
    var assumptionSyntaxLeft: string[] = [];
    var assumptionSyntaxRight: string[] = [];

    x.assumptions.forEach(v => {
        assumptionSyntaxLeft.push(getInternalSyntaxHTML(v, false, true));
        assumptionSyntaxRight.push(getFormalSyntax(v, 0, null, [...x.assumptions, x.goal]));
    });

    htmlString += assumptionSyntaxLeft.join(", ");

    htmlString += "<div class='rightBracket'>]</div></div></div></div></div>";
    // End left

    // Middle
    htmlString += '<div class="middle' + (!editModeOn ? ' shrink' : '') + '">' + (undefInductivesWithoutUnknowns[j] !== undefined ? getRuleHTML(x) : "&nbsp;") + '</div>';

    // End middle

    // Right
    htmlString += '<div class="right formal' + (!editModeOn ? ' fill' : '') + '">';

    // Indention
    htmlString += '<div class="indentProof" data-indent="' + n + '">';

    // Assumptions
    htmlString += '<div class="assumptions"><div class="leftBracket">[</div>' + assumptionSyntaxRight.join('<div class="comma">,</div>') + '<div class="rightBracket">]</div></div>';

    // Goal
    htmlString += '<div class="goal">' + getFormalSyntax(x.goal, 0, null, [...x.assumptions, x.goal]) + '</div>';
    htmlString += '</div>';

    htmlString += '</div>';
    // End right

    htmlString += '</div>';

    $(htmlString).appendTo("#frameContainer");

    i += 1;
    j += 1;

    x.premises.forEach(v => {
        var a = appendLines(v, n + 1, i, j);
        i = a[0];
        j = a[1];
    });

    // Write "news" line
    if (x.premises.length > 0 && (x instanceof synUniI || x instanceof synExiE && !(<synExiE>x).waitingForPCompletion)) {
        writeNewsLine(x, n + 1, i);
        i += 1;
    }

    return [i, j];
}

function writeNewsLine(x: Inductive, n: number, i: number) {

    var htmlString: string = "<div class=\"line\">";

    // Line numbering
    htmlString += '<div class="lineNumber">' + i + '</div>';

    // Left
    htmlString += '<div class="left code' + (!editModeOn ? ' hidden' : '') + '">';

    htmlString += '<div class="indentProof" data-indent="' + n + '">';

    // Write "news c <list>"
    htmlString += "<div class='synGoal'><div class='news'>news</div>";

    if (x instanceof synUniI)
        htmlString += '<div class="arg">' + getInternalSyntaxHTML((<synUniI>x).c) + '</div>';
    else if (x instanceof synExiE)
        htmlString += '<div class="arg">' + getInternalSyntaxHTML((<synExiE>x).c) + '</div>';

    htmlString += '<div class="arg leftParentheses">(</div>';

    var newsList: string[][] = [];

    if (x instanceof synExiE)
        newsList.push([getInternalSyntaxHTML((<fmExi>x.premises[0].goal).fm)]);

    if (x instanceof synUniI || x instanceof synExiE) {
        newsList.push([getInternalSyntaxHTML(x.goal)]);
    }

    newsList.push([]);
    x.assumptions.forEach(v => {
        newsList[newsList.length - 1].push(getInternalSyntaxHTML(v));
    });

    var htmlAppend: string[] = [];

    newsList.forEach(v => {
        htmlAppend.push("<div class='leftBracket'>[</div>" + v.join('<div class="comma">,</div><wbr />') + "<div class='rightBracket'>]</div>");
    });

    htmlString += htmlAppend.join("<div class='concat'>#</div>");

    htmlString += '<div class="rightParentheses">)</div>';
    htmlString += '</div></div></div>';

    htmlString += '<div class="middle' + (!editModeOn ? ' shrink' : '') + '">*</div>';
    // End middle

    // Right
    htmlString += '<div class="right formal' + (!editModeOn ? ' fill' : '') + '">';

    // Indention
    htmlString += '<div class="indentProof" data-indent="' + n + '">';

    // Goal
    htmlString += '<div class="leftParentheses">(</div>';
    htmlString += '<div class="id">' + getFormalSyntax((<synExiE>x).c, 0, null, []) + '</div>';
    htmlString += '<div class="rightParentheses">)</div>';

    htmlString += '</div>';

    htmlString += '</div>';
    // End right

    $(htmlString).appendTo($("#frameContainer"));
}

//
// Search/replace functions
//

function replaceFormalSymbols(selection: any, customReplaces: { s: RegExp; r: string }[] = []): void {

    $(selection).each((i, e) => {


        // Subscript
        $(e).html(($(e).html().replace(/\*/g, '\'')));

        customReplaces.forEach(rp => {
            $(e).html(($(e).html().replace(rp.s, rp.r)));
        })
    });

}

//
// Misc
//

function updateExistingIndexUnknowns() {
    // Update the indices of the HTML elements of unknowns
    $("#frameContainer .line .left a").not(".newSynRule").each((i, e) => {
        $(e).data("indexUnknown", i);
    });

    $(".middle").each((i, e) => {
        $("a", e).data("synUnknownIndex", i);
    });
}


var editModeOn = false;

function attachClickEvents() {
    // Attach click handlers to menu elements
    $("#header .load").on("click", e => {
        setTitle("Load");

        closeOverlays();

        newCenteredOverlay("load", (x: Inductive[]) => {
            loadProof(x);
        });
    });

    $("#header .code").on("click", e => {
        setTitle("Code");

        newCenteredOverlay("code", () => {
        });
    });

    $("#header .help").on("click", e => {
        setTitle("Help");

        newCenteredOverlay("help", () => {
        });
    });

    $("#header .verify").on("click", e => {
        setTitle("Verify");

        newCenteredOverlay("verify", () => {
        });
    });

    $(document).ready(function () {
        if (!window.location.hash)
            $("#header .help").click();
    });

    $("#header .undo").click(e => {
        var e = jQuery.Event("keydown");
        e.which = 46;
        e.keyCode = 46;
        $(document).trigger(e);
    });

    $("#header .stop").click(e => {
        var e = jQuery.Event("keydown");
        e.which = 45;
        e.keyCode = 45;
        $(document).trigger(e);
    });

    $(document).on("click", "#frame", e => {
        editModeOn = !editModeOn;

        update();
    });

    $(document).on("click", "a", e => {
        e.stopImmediatePropagation();
    });
}

function attachHashEventListeners() {
    // Check for browser support
    if (!("onhashchange" in window)) {
        console.log("Cannot load proofs through hash event listener: No browser support.");
        return;
    }

    // Hash change event
    $(window).on("hashchange", () => {
        // No hash value
        if (!window.location.hash)
            return;

        // Remove leading #
        var hashValue = window.location.hash.substring(1);

        // Match against number value
        var match = hashValue.search(/^([0-9]+)$/) !== -1;

        // No match
        if (!match)
            return;

        var proofID = "Hint " + hashValue;

        if (proofCodes[proofID] === undefined)
            return;

        var proof = decodeProof(proofCodes[proofID]);

        if (proof !== null) {
            closeAllOverlays();

            loadProof(proof, true);
        }

        setTitle();
    });
}


/*
 * New overlay
 */

function newOverlay(t: JQueryEventObject, type: string, cb: (...input) => any, ...input): void {
    var overlay = $("<div class=\"overlay\" style=\"display: none;\"></div > ");

    // Position overlay at position of clicked element
    var coords = $(t.currentTarget).offset();
    overlay.css({
        position: "absolute",
        left: (coords.left) + "px",
        top: (coords.top) + "px",
        marginLeft: "0.8vw",
        marginTop: "1.5vw"
    });

    $("body").append(overlay);

    switch (type) {
        case "newSynRule":
            /* Remove old overlays */
            closeOverlays(overlay);

            addInnerNewSynRule(overlay, cb, input[0]);
            break;
        case "newFormula":
            closeOverlays(overlay);

            addInnerNewFormula(overlay, cb);
            break;
        case "newID":
            closeOverlays(overlay);

            addInnerNewID(overlay, cb, input[0]);
            break;
        case "newTms":
            closeOverlays(overlay);

            addInnerNewTms(overlay, cb, input[0]);
            break;
        case "newTm":
            closeOverlays(overlay);

            addInnerNewSingleTm(overlay, cb, input[0]);
            break;
        case "existingTerm":
            closeOverlays(overlay);

            selectExistingTerm(overlay, cb, input[0]);
            break;
        default:
            throw new Error("Could not get overlay of type: " + type);
    }

    overlay.prepend("<div class=\"closeOverlay\">X</div>");
    overlay.show();

    $(".closeOverlay", overlay).click(function (e) {
        closeOverlays();
    });
}

function closeOverlays(...exceptions: JQuery[]) {
    var selection = $(".overlay");

    exceptions.forEach((v) => {
        selection = selection.not(v);
    });

    selection.remove();
};

function closeAllOverlays() {
    closeOverlays();
    $(".centeredOverlayOuter").remove();
}

function closeTopOverlay() {
    var overlay = $(".overlay:last", $("body"));

    if (overlay.parent(".centeredOverlayOuter").length > 0) {
        overlay.parent(".centeredOverlayOuter").remove();
    } else {
        overlay.remove();
    }
}

//
// New centered overlay
//

function newCenteredOverlay(olType: string, cb: (...input) => any, ...input): void {
    var outer = $("<div class=\"centeredOverlayOuter\"></div>");

    var content = $("<div class=\"overlay\"></div>");

    content.hide();

    outer.append(content);
    $("body").append(outer);

    switch (olType) {
        case "load":

            loadInner(content, cb);

            break;
        case "code":

            codeInner(content, cb);

            break;
        case "help":

            helpInner(content, cb);

            break;
        case "verify":

            verifyInner(content, cb);

            break;
        default:
            throw new Error("Could not get overlay of type: " + olType);

    }

    content.prepend("<div class=\"closeCenteredOverlay\"><div>X</div></div>");
    content.show();

    $(".closeCenteredOverlay", content).click(function (e) {
        $(outer).remove();
        setTitle();
    });
}

/*
 * The different overlays
 */

function addInnerNewSynRule(overlay: JQuery, callback: (x: Inductive) => void, y: Inductive): void {
    var r = $("<div></div>");
    overlay.append(r);

    // Only add applicable rules to list of options
    if (synBool.isApplicable(y.goal))
        r.append("<a class=\"newSynBoole\">Boole</a><br />");

    if (synImpE.isApplicable(y.goal))
        r.append("<a class=\"newSynImpE\">Imp_E</a><br />");

    if (synImpI.isApplicable(y.goal))
        r.append("<a class=\"newSynImpI\">Imp_I</a><br />");
    if (synDisE.isApplicable(y.goal))
        r.append("<a class=\"newSynDisE\">Dis_E</a><br />");

    if (synDisI1.isApplicable(y.goal))
        r.append("<a class=\"newSynDisI1\">Dis_I1</a><br />");

    if (synDisI2.isApplicable(y.goal))
        r.append("<a class=\"newSynDisI2\">Dis_I2</a><br />");

    if (synConE1.isApplicable(y.goal))
        r.append("<a class=\"newSynConE1\">Con_E1</a><br />");

    if (synConE2.isApplicable(y.goal))
        r.append("<a class=\"newSynConE2\">Con_E2</a><br />");

    if (synConI.isApplicable(y.goal))
        r.append("<a class=\"newSynConI\">Con_I</a><br />");

    if (synExiE.isApplicable(y.goal))
        r.append("<a class=\"newSynExiE\">Exi_E</a><br />");

    if (synExiI.isApplicable(y.goal))
        r.append("<a class=\"newSynExiI\">Exi_I</a><br />");

    if (synUniE.isApplicable(y.goal))
        r.append("<a class=\"newSynUniE\">Uni_E</a><br />");

    if (synUniI.isApplicable(y.goal))
        r.append("<a class=\"newSynUniI\">Uni_I</a><br />");


    $("a", r).click(function (e) {
        // Initialize structure of selected rule and send it to callback
        var newIndClass: Inductive;

        var className: String = $(e.currentTarget).prop("class").split(/\s+/).shift();

        if (className === "newSynBoole") {
            newIndClass = new synBool(y.goal, y.assumptions);
        }

        else if (className === "newSynImpE") {
            newIndClass = new synImpE(y.goal, y.assumptions);
        }

        else if (className === "newSynImpI") {
            newIndClass = new synImpI(y.goal, y.assumptions);
        }

        else if (className === "newSynDisE") {
            newIndClass = new synDisE(y.goal, y.assumptions);
        }

        else if (className === "newSynDisI1") {
            newIndClass = new synDisI1(y.goal, y.assumptions);
        }

        else if (className === "newSynDisI2") {
            newIndClass = new synDisI2(y.goal, y.assumptions);
        }

        else if (className === "newSynConE1") {
            newIndClass = new synConE1(y.goal, y.assumptions);
        }

        else if (className === "newSynConE2") {
            newIndClass = new synConE2(y.goal, y.assumptions);
        }

        else if (className === "newSynConI") {
            newIndClass = new synConI(y.goal, y.assumptions);
        }

        else if (className === "newSynExiE") {
            newIndClass = new synExiE(y.goal, y.assumptions);
        }

        else if (className === "newSynExiI") {
            newIndClass = new synExiI(y.goal, y.assumptions);
        }

        else if (className === "newSynUniE") {
            newIndClass = new synUniE(y.goal, y.assumptions);
        }

        else if (className === "newSynUniI") {
            newIndClass = new synUniI(y.goal, y.assumptions);
        }

        closeOverlays();

        callback(newIndClass);
    });
}

function addInnerNewFormula(overlay: JQuery, callback: (x: Formula) => void): void {
    var r = $("<div></div>");
    overlay.append(r);

    r.append("<div>Formulas:</div>");
    r.append("<a class=\"newFmFalsity\">Falsity</a><br />");
    r.append("<a class=\"newFmPre\">Predicate</a><br />");
    r.append("<a class=\"newFmImp\">Implication</a><br />");
    r.append("<a class=\"newFmDis\">Disjunction</a><br />");
    r.append("<a class=\"newFmCon\">Conjunction</a><br />");
    r.append("<a class=\"newFmExi\">Existential Quantifier</a><br />");
    r.append("<a class=\"newFmUni\">Universal Quantifier</a>");

    $("a", r).click(function (e) {

        var newFm: Formula;

        var className: String = $(e.currentTarget).prop("class").split(/\s+/).shift();

        if (className === "newFmFalsity") {
            newFm = new fmFalsity();
        }

        else if (className === "newFmPre") {
            newFm = new fmPre(null, null);
        }

        else if (className === "newFmImp") {
            newFm = new fmImp(null, null);
        }

        else if (className === "newFmDis") {
            newFm = new fmDis(null, null);
        }

        else if (className === "newFmCon") {
            newFm = new fmCon(null, null);
        }

        else if (className === "newFmExi") {
            newFm = new fmExi(null);
        }

        else if (className === "newFmUni") {
            newFm = new fmUni(null);
        }

        callback(newFm);

        closeOverlays();
    });
}


function addInnerNewID(overlay: JQuery, callback: (x: string) => void, capitalLettersFirst: boolean): void {
    var r = $("<div></div>");
    overlay.append(r);

    r.append("<div>New ID:</div>");
    var select = $("<select></select>");
    r.append(select);

    if (capitalLettersFirst) {
        for (var i = 65; i <= 90; i++) {
            select.append("<option>" + String.fromCharCode(i) + "</option>");
        }

        for (var i = 97; i <= 122; i++) {
            select.append("<option>" + String.fromCharCode(i) + "</option>");
        }
    } else {
        for (var i = 97; i <= 122; i++) {
            select.append("<option>" + String.fromCharCode(i) + "</option>");
        }

        for (var i = 65; i <= 90; i++) {
            select.append("<option>" + String.fromCharCode(i) + "</option>");
        }
    }

    select.append("<option>c*</option>");
    select.append("<option>c**</option>");
    select.append("<option>c***</option>");

    r.append("<div><input type=\"submit\" value=\"Done\" /></div>");

    $(":submit", r).click(function (e) {

        var newID: string = $("select", r).val();

        callback(newID);

        closeOverlays();
    });
}


function addInnerNewTms(overlay: JQuery, callback: (x: number, y: number[]) => void, indexUnknown: number): void {
    var r = $("<div></div>");
    overlay.append(r);

    r.append("<div>New list of terms:</div>");

    var terms = r.append("<div class=\"terms\"></div>");
    var select = $("<select style='display: block;'></select>");

    select.append("<option value='-1'>Function</option>");
    select.append("<optgroup label='Variable'>");
    for (var i = 0; i <= 20; i++) {
        select.append("<option>" + i + "</option>");
    }
    select.append("</optgroup>");


    r.append("<div class=\"buttons\">");
    r.append("<input type=\"submit\" value=\"Done\" />");
    r.append("<input type=\"button\" class=\"addTerm\" value=\"Add term\" />");
    r.append("<input type=\"button\" class=\"removeTerm\" value=\"Remove last term\" />");
    r.append("</div>");

    $(":submit", r).click(function (e) {

        var tms: number[] = [];
        var test: boolean[] = [];

        // Check if same term has been selected more than once
        var interrupt = false;
        $("select", r).each((i, e) => {
            if ($(e).val() === null) {
                alert("Please select all terms");
                interrupt = true;
                return false;
            }

            var v = parseInt($(e).val(), 10);

            tms.push(v);

            if (v === -1)
                return true;

            test[v] = true;
        });

        if (interrupt)
            return false;

        callback(indexUnknown, tms);

        closeOverlays();
    });

    $(".addTerm:button").click(() => {
        select.clone().val("-1").appendTo($(".terms", r));
    });

    $(".removeTerm:button").click(() => {
        $("select:last", $(".terms", r)).remove();
    });
}


function addInnerNewSingleTm(overlay: JQuery, callback: (x: number, y: number[]) => void, indexUnknown: number): void {
    var r = $("<div></div>");
    overlay.append(r);

    r.append("<div>New term:</div>");

    var terms = r.append("<div class=\"terms\"></div>");
    var select = $("<select style='display: block;'></select>");

    select.append("<option value='-1'>Function</option>");
    select.append("<optgroup label='Variable'>");
    for (var i = (currentState.xs[indexUnknown].parent && currentState.xs[indexUnknown].parent.x instanceof synExiI ? currentState.xs[indexUnknown].parent.nq : 0); i <= 20; i++) {
        select.append("<option>" + i + "</option>");
    }
    select.append("</optgroup>");

    select.appendTo($(".terms", r));

    r.append("<div class=\"buttons\">");
    r.append("<input type=\"submit\" value=\"Done\" />");
    r.append("</div>");

    $(":submit", r).click(function (e) {
        var v = parseInt($("select", r).val(), 10);

        callback(indexUnknown, [v]);

        closeOverlays();
    });
}


function selectExistingTerm(overlay: JQuery, callback: (x: { term: Term, occs?: number[] }[]) => void, p: Inductive): void {
    var r = $("<div></div>");
    overlay.append(r);

    r.append("<div>Formula:</div>");
    r.append('<div class="formula">' + getFormalSyntax(p.goal, 0, null, [...p.assumptions, p.goal]) + '</div><br />');

    r.append("<div>Existing term in formula to quantify:</div>");

    var terms = r.append("<div class=\"terms\"></div>");

    var select = $("<select></select>");
    var selectVars = $('<optgroup label="Variables"></optgroup>');
    var selectFns = $('<optgroup label="Functions"></optgroup>');

    // Link terms occuring multiple times
    var ts: { t: Term; linkedTo: Term[] }[] = [];

    getFreeTerms(p.goal).forEach(e => {
        var x: { t: Term; linkedTo: Term[] };

        var newTerm: Term = e.t;

        for (var i = 0; i < e.nq; i++) {
            newTerm = dect(newTerm);
        }

        ts.some(d => {
            if (equalFormulas(newTerm, d.t)) {
                x = d;
                return true;
            }
        });

        if (x === undefined) {
            ts.push({ t: newTerm, linkedTo: [] });
        } else {
            x.linkedTo.push(newTerm);
        }
    });

    // Add each term to list of functions or list of variables (term types)
    ts.forEach((e, i) => {
        (e.t instanceof tmVar ? selectVars : selectFns)
            .append("<option value='" + i + "'>" + getFormalSyntax(e.t, 0, null, [...p.assumptions, p.goal]) + "</option>");
    });

    if (selectVars.children("option").length > 0)
        select.append(selectVars);
    if (selectFns.children("option").length > 0)
        select.append(selectFns);

    // Append select to overlay
    select.appendTo(terms);

    // Add button to close overlay
    r.append('<br /><div><input type="button" value="Ok" />');

    // Select onChange handler
    $(select).on("change", e => {
        // Remove any existing term occurence selectors
        $("div.selectOccurences", r).remove();

        // Get index of chosen term in list
        var i: number = $(e.currentTarget).val();

        if (ts[i].linkedTo.length > 0) {
            // Create and add new div
            var o = $('<div class="selectOccurences"></div>');
            select.after(o);

            o.append("<br /><div>Select occurences</div>");

            for (var k = 0; k < ts[i].linkedTo.length + 1; k++) {
                o.append((k + 1) + '. <input type="checkbox" checked /><br />');
            }
        }

    }).change();

    // Button click handler
    $(":button", r).on("click", e => {
        // Get chosen occurences, if needed
        var i: number = select.val();

        var cbt: { term: Term, occs: number[] }[] = [];

        if (ts[i].linkedTo.length == 0)
            cbt.push({ term: ts[i].t, occs: [0] });

        else {
            var termOccs = { term: ts[i].t, occs: [] };

            $(":checkbox", r).each((j, e) => {
                if ($(e).prop("checked"))
                    termOccs.occs.push(j);
            });

            cbt.push(termOccs);
        }

        // Simple error check: Make sure that term list is not empty
        if (cbt.length == 0)
            alert("You have not selected any occurences of the term to quantify");
        else {
            callback(cbt);
            closeOverlays();
        }
    });
}

function loadInner(overlay: JQuery, callback: (x: Inductive[]) => void): void {
    // Main div to contain contents
    var content = $("<div class=\"flexContentY\"></div>");
    overlay.append(content);

    // Make menu buttons (contained in a div)
    var buttonsContainer = $("<div class=\"buttonContainer\"></div>");
    var buttonsTable = $("<div class=\"buttonsTable\"></div>");
    var buttonsRow = $("<div class=\"buttonsRow\"></div>");

    var btnLeft = $('<div class="btnLeft"></div>');
    var btnMid = $('<div class="btnMid"></div>');
    var btnRight = $('<div class="btnRight"></div>');

    buttonsRow.append(btnLeft);
    buttonsRow.append(btnMid);
    buttonsRow.append(btnRight);

    buttonsContainer.append(buttonsTable);
    buttonsTable.append(buttonsRow);

    var cancel = $('<div class="button small">Cancel load</div>');
    var update = $('<div class="button small">Load shown proof</div>');
    var currentProof = $('<div class="button small">The current proof</div>');

    var allProofs = $('<div class="button small exampleProof">All proofs</div>');

    btnLeft.append(cancel);
    btnMid.append(currentProof);
    btnMid.append(allProofs);
    btnRight.append(update);

    // Example buttons
    var examplesJQuery: JQuery[] = [];

    for (var i = 0; i <= 9; i++) {
        examplesJQuery[i] = $('<div class="button small exampleProof">Test ' + i + '</div>');
        examplesJQuery[i].data("ithExample", i);

        btnMid.append(examplesJQuery[i]);
    }

    var testSuite = $('<div class="button small exampleProof">Proof index</div>');
    btnMid.append(testSuite);

    content.append(buttonsContainer);

    // Textarea
    var textareaContainer = $('<div class="loadTextareaContainer"></div>');

    var textarea = $("<textarea class=\"loadTextarea\" spellcheck='false'></textarea>");

    textareaContainer.append(textarea);
    content.append(textareaContainer);

    // Apply button events
    cancel.click(e => {
        $(".closeCenteredOverlay", overlay).trigger("click");
    });

    update.click(e => {
        var proofString = (<string>textarea.val()).trim();

        if (proofString == "")
            proofString = INITIAL_PROOF;

        var newProofs = decodeProof(proofString);

        if (newProofs === undefined || newProofs === null) {
            textarea.css({ borderColor: "red" });

            setTimeout(() => {
                textarea.css({ borderColor: "blue" });
            }, 2000);

        } else {
            callback(newProofs);

            cancel.trigger("click");
        }
    });

    // Click handler to insert correct proof code on example button click
    $(".exampleProof").on("click", v => {
        if ($(v.currentTarget).data("ithExample") !== undefined)
            textarea.val(proofCodes["Test " + $(v.currentTarget).data("ithExample")]);

        else if ($(v.currentTarget).html() === "Proof index")
            textarea.val(proofCodes["Proof index"]);

        else if ($(v.currentTarget).html() === "All proofs")
            textarea.val(proofCodes["All proofs"]);
    });

    // Present proof code with prepended comment lines
    var presentProofCode = ". The current proof is available in the lines shown here.\n. Use text copy-and-paste to a file in order to save it.\n. The proof lines can be edited or replaced entirely.\n. A line starting with a period is a comment only.\n\n";

    for (var i = stateStack.stack.length - 1; i >= 0; i--)
        presentProofCode += encodeProof(stateStack.stack[i].p) + "\n";

    currentProof.on("click", () => {
        textarea.val(presentProofCode);
    });

    // Add hover effect to active button
    $(".btnLeft, .btnMid, .btnRight").children().on("click", () => {
        $(".btnMid").children().removeClass("buttonMidHover");
    });

    $(".btnMid").children().on("click", e => $(e.currentTarget).addClass("buttonMidHover"));

    currentProof.trigger("click");
};

function codeInner(overlay: JQuery, callback: () => void): void {
    // Flexible content
    var content = $("<div class=\"flexContentY\"></div>");
    overlay.append(content);

    // Make menu buttons
    var buttonsContainer = $("<div class=\"buttonContainer\"></div>");
    var buttonsTable = $("<div class=\"buttonsTable\"></div>");
    var buttonsRow = $("<div class=\"buttonsRow\"></div>");

    var btnLeft = $('<div class="btnLeft"></div>');
    var btnMid = $('<div class="btnMid"></div>');
    var btnRight = $('<div class="btnRight"></div>');

    buttonsRow.append(btnLeft);
    buttonsRow.append(btnMid);
    buttonsRow.append(btnRight);

    buttonsContainer.append(buttonsTable);
    buttonsTable.append(buttonsRow);

    var cancel = $('<div class="button small">Cancel code</div>');
    var folButton = $('<div class="button small">Definition of first-order logic syntax and semantics</div>');
    var ndButton = $('<div class="button small">Definition of natural deduction proof system</div>');
    var sampleButton = $('<div class="button small">Notes on Isabelle formalization code</div>');
    var isaFileButton = $('<div class="button small">Show Isabelle theory file</div>');

    btnLeft.append(cancel);
    btnMid.append(ndButton);
    btnMid.append(folButton);
    btnMid.append(sampleButton);
    btnRight.append(isaFileButton);

    content.append(buttonsContainer);

    // Content box
    var helpContent = $('<div class="helpContent"></div>');
    content.append(helpContent);

    var ParenthesesBracketReplace = (s: string) => {
        return s.replace(/\(/gm, '<div class="leftParentheses">(</div>')
            .replace(/\)/gm, '<div class="rightParentheses">)</div>')
            .replace(/\[/gm, '<div class="leftBracket">[</div>')
            .replace(/\]/gm, '<div class="rightBracket">]</div>');
    }


    // Table of rules (function is made to generate the tables in a more generic way)
    var getRuleTable = (name: string, premises: string[], goal: string) => {
        var ndContentStr = "";
        ndContentStr += '<table cellpadding="0" cellspacing="0" border="0" class="ndRule">';
        ndContentStr += '<tr class="premises">';
        premises.forEach(v => {
            ndContentStr += '<td>' + ParenthesesBracketReplace(v) + '</td>';
        });
        ndContentStr += '<td>&nbsp;</td>';
        ndContentStr += '</tr>';
        ndContentStr += '<tr>';
        ndContentStr += '<td colspan="' + premises.length + '">';
        ndContentStr += '<table cellpadding="0" cellspacing="0" border="0" style="width: 100%;">';
        ndContentStr += '<tr>';
        ndContentStr += '<td><div class="thinline"></div></td>';
        ndContentStr += '</tr>';
        ndContentStr += '</table>';
        ndContentStr += '</td>';
        ndContentStr += '<td class="name"">' + name + '</td>';
        ndContentStr += '</tr>';
        ndContentStr += '<tr>';
        ndContentStr += '<td colspan="' + premises.length + '" class="goal">' + ParenthesesBracketReplace(goal) + '</td>';
        ndContentStr += '<td>&nbsp;</td>';
        ndContentStr += '</tr>';
        ndContentStr += '</table>';

        return ndContentStr;
    };

    // Tabs
    /* Content: Isabelle */
    var isabelleContent = $('<div>' + (isabelleFileFormatted.length > 0 ? "<pre class='isabelleFileView'>" + isabelleFileFormatted + "</pre>" : 'Cannot show Isabelle theory file: "' + indexNadeaURL.replace("index.nadea", "NaDeA.thy") + '"') + '</div>');

    /* Content: Def. of syntax and semantics */
    var dssContent = $('<div></div>');
    dssContent.append(ParenthesesBracketReplace('<div class="codeBlock"><div class="textline extraSpace">The natural deduction proof system assumes the following definition of first-order logic syntax and semantics:</div><div class="textline"><strong>Syntax</strong></div><div class=\"textline extraSpace\">A function/predicate identifier is a list of characters which can be written ' + nadeaQuot + '...' + nadeaQuot + '.</div><div class="textline lessSpace\">identifier <span class=\"eqdef\">:=</span> [char, ..., char]</div><div class="textline lessSpace\">term <span class=\"eqdef\">:=</span> Var nat <span class=\"delimiter\">|</span> Fun identifier [term, ..., term]</div><div class="textline lessSpace\">formula <span class=\"eqdef\">:=</span> Falsity <span class=\"delimiter\">|</span> Pre identifier [term, ..., term] <span class=\"delimiter\">|</span> <span>Imp</span> formula formula <span class=\"delimiter\">|</span> <span>Dis</span> formula formula <span class=\"delimiter\">|</span> <span>Con</span> formula formula <span class=\"delimiter\">|</span> <span>Exi</span> formula <span class=\"delimiter\">|</span> <span>Uni</span> formula<br /></div><br /><div class="textline">The quantifiers use de Bruijn indices') + ' (natural numbers) ' + ParenthesesBracketReplace('and truth, negation and biimplication are abbreviations.</div><br /><div class="textline"><strong>Semantics</strong></div><div class="textline extraSpace">The domain of quantification is implicit in the environment ´e´ for variables and in the function semantics ´f´ and predicate semantics ´g´ of arbitrary arity.</div></div><div class="leftColumn noTopMargin codeBlock">semantics_term e f (Var n) <span class=\"eqdef\">=</span> e n<br />semantics_term e f (Fun i l) <span class=\"eqdef\">=</span> f i (semantics_list e f l)<br /><br />semantics_list e f [] <span class=\"eqdef\">=</span> []<br />semantics_list e f (t # l) <span class=\"eqdef\">=</span> semantics_term e f t <span class=\"headtail\">#</span> semantics_list e f l<br /><div class="textline"><br />Operator # is between the head and the tail of a list.</div></div><div class="rightColumn noTopMargin codeBlock">semantics e f g Falsity <span class=\"eqdef\">=</span> False<br />semantics e f g (Pre i l) <span class=\"eqdef\">=</span> g i (semantics_list e f l)<br />semantics e f g (<span class="impFm">Imp</span> p q) <span class=\"eqdef\">=</span> (if semantics e f g p then semantics e f g q else True)<br />semantics e f g (<span class="disFm">Dis</span> p q) <span class=\"eqdef\">=</span> (if semantics e f g p then True else semantics e f g q)<br />semantics e f g (<span class="conFm">Con</span> p q) <span class=\"eqdef\">=</span> (if semantics e f g p then semantics e f g q else False)<br />semantics e f g (<span class="exiFm">Exi</span> p) <span class=\"eqdef\">=</span> (<span class=\"qmark\">?</span> x. semantics (% n. if n = 0 then x else e (n - 1)) f g p)<br />semantics e f g (<span class="uniFm">Uni</span> p) <span class=\"eqdef\">=</span> (<span class=\"exmark\">!</span> x. semantics (% n. if n = 0 then x else e (n - 1)) f g p)<br /><br /></div><div class="clear"></div><div class="codeBlock"><div class="textline">Operator % is for lambda abstraction, operator ! is for universal quantification and operator ? is for existential quantification.</div><br /><div class="textline extraSpace">All meta-variables are implicitly universally quantified in the following derived rule connecting the provability predicate ´OK´ and the semantics:</div>') + '<div class="ndRulesContainer first">' + getRuleTable("Soundness", ["OK p []"], "semantics e f g p") + '<div class="clear"></div></div></div><br /><div class="textline">The computer-checked soundness proof is provided in the Isabelle theory file here: https://github.com/logic-tools/nadea</div>');

    /* Sample proofs and exercises with hints */
    var sampleContent = $('<div>' +
        '<div class="codeBlock">' +
        '<div class="textline extraSpace">In type declarations &#39;a is for an arbitrary type and => is used for function space.</div>' +
        '<div class="columnContainer extraSpace">' +
        '<div class="column2">' +
        '<div class="table"></div>' +
        '</div>' +
        '<div class="column2">' +
        '<div class="table"></div>' +
        '</div>' +
        '<div class="clear"></div>' +
        '</div>' +
        '<div class="textline">==> is meta-implication (used in inductive definitions and in theorems).</div>' +
        '</div>' +
        '</div>');
    var sampleContentKeywordTableA = $(".table:eq(0)", sampleContent);
    var sampleContentKeywordTableB = $(".table:eq(1)", sampleContent);

    isabelleKeyWords.slice(0, Math.ceil(isabelleKeyWords.length / 2)).forEach(obj => {
        sampleContentKeywordTableA.append('<div class="tableRow">' +
            '<div class="tableCell"><strong>' + obj.keyword + '</strong></div>' +
            '<div class="tableCell">' + obj.description + '</div>' +
            '</div>');
    });

    isabelleKeyWords.slice(Math.ceil(isabelleKeyWords.length / 2)).forEach(obj => {
        sampleContentKeywordTableB.append('<div class="tableRow">' +
            '<div class="tableCell"><strong>' + obj.keyword + '</strong></div>' +
            '<div class="tableCell">' + obj.description + '</div>' +
            '</div>');
    });

    /* Summary of rules */
    var sorContent = $('<div></div>');

    sorContent.append('<div class="textline codeBlock extraSpace">The natural deduction proof system is defined by the provability predicate ´OK´ using the auxiliary predicate ´news´ (new identifier in formulas) and the auxiliary function ´sub´ (substitution for variable in formula):</div>');

    // Rule tables are created.
    var divBox1 = $('<div class="ndRulesContainer first"></div>');
    var divBox2 = $('<div class="ndRulesContainer"></div>');
    var divBox3 = $('<div class="ndRulesContainer"></div>');

    divBox1.append(getRuleTable("Assume", ["member p z"], "OK p z"));
    divBox1.append(getRuleTable("Boole", ["OK Falsity ((Imp p Falsity) # z)"], "OK p z"));
    divBox1.append(getRuleTable("Imp_E", ["OK (Imp p q) z", "OK p z"], "OK q z"));
    divBox1.append(getRuleTable("Imp_I", ["OK q (p # z)"], "OK (Imp p q) z"));
    divBox1.append('<div class="floatRightComment">Operator # is between the head and the tail of a list.</div>');

    divBox2.append(getRuleTable("Dis_E", ["OK (Dis p q) z", "OK r (p # z)", "OK r (q # z)"], "OK r z"));
    divBox2.append(getRuleTable("Dis_I1", ["OK p z"], "OK (Dis p q) z"));
    divBox2.append(getRuleTable("Dis_I2", ["OK q z"], "OK (Dis p q) z"));
    divBox2.append(getRuleTable("Con_E1", ["OK (Con p q) z"], "OK p z"));
    divBox2.append(getRuleTable("Con_E2", ["OK (Con p q) z"], "OK q z"));
    divBox2.append(getRuleTable("Con_I", ["OK p z", "OK q z"], "OK (Con p q) z"));

    divBox3.append(getRuleTable("Exi_E", ["OK (Exi p) z", "OK q ((sub 0 (Fun c []) p) # z)", "news c (p # q # z)"], "OK q z"));
    divBox3.append(getRuleTable("Exi_I", ["OK (sub 0 t p) z"], "OK (Exi p) z"));
    divBox3.append(getRuleTable("Uni_E", ["OK (Uni p) z"], "OK (sub 0 t p) z"));
    divBox3.append(getRuleTable("Uni_I", ["OK (sub 0 (Fun c []) p) z", "news c (p # z)"], "OK (Uni p) z"));

    sorContent.append(divBox1);
    sorContent.append(divBox2);
    sorContent.append(divBox3);

    sorContent.append('<div class="clear"></div>');

    // Content: Summary of rules
    sorContent.append(ParenthesesBracketReplace('<div class=\"leftColumn codeBlock\">member p [] = False<br />member p (q # z) <span class=\"eqdef\">=</span> (if p = q then True else member p z)<br /><br />new_term c (Var n) <span class=\"eqdef\">=</span> True<br />new_term c (Fun i l) <span class=\"eqdef\">=</span> (if i = c then False else new_list c l)<br /><br />new_list c [] <span class=\"eqdef\">=</span> True<br />new_list c (t # l) <span class=\"eqdef\">=</span> (if new_term c t then new_list c l else False)<br /><br />new c Falsity <span class=\"eqdef\">=</span> True<br />new c (Pre i l) <span class=\"eqdef\">=</span> new_list c l<br />new c (<span class="impFm">Imp</span> p q) <span class=\"eqdef\">=</span> (if new c p then new c q else False)<br />new c (<span class="disFm">Dis</span> p q) <span class=\"eqdef\">=</span> (if new c p then new c q else False)<br />new c (<span class="conFm">Con</span> p q) <span class=\"eqdef\">=</span> (if new c p then new c q else False)<br />new c (<span class="exiFm">Exi</span> p) <span class=\"eqdef\">=</span> new c p<br />new c (<span class="uniFm">Uni</span> p) <span class=\"eqdef\">=</span> new c p<br /><br />news c [] <span class=\"eqdef\">=</span> True<br />news c (p # z) <span class=\"eqdef\">=</span> (if new c p then news c z else False)</div><div class=\"rightColumn codeBlock\">inc_term (Var n) <span class=\"eqdef\">=</span> Var (n + 1)<br />inc_term (Fun i l) <span class=\"eqdef\">=</span> Fun i (inc_list l)<br /><br />inc_list [] <span class=\"eqdef\">=</span> []<br />inc_list (t # l) <span class=\"eqdef\">=</span> inc_term t <span class=\"headtail\">#</span> inc_list l<br /><br />sub_term v s (Var n) <span class=\"eqdef\">=</span> (if n < v then Var n else if n = v then s else Var (n - 1))<br />sub_term v s (Fun i l) <span class=\"eqdef\">=</span> Fun i (sub_list v s l)<br /><br />sub_list v s [] <span class=\"eqdef\">=</span> []<br />sub_list v s (t # l) <span class=\"eqdef\">=</span> sub_term v s t <span class=\"headtail\">#</span> sub_list v s l<br /><br />sub v s Falsity <span class=\"eqdef\">=</span> Falsity<br />sub v s (Pre i l) <span class=\"eqdef\">=</span> Pre i (sub_list v s l)<br />sub v s (<span class="impFm">Imp</span> p q) <span class=\"eqdef\">=</span> <span class="impFm">Imp</span> (sub v s p) (sub v s q)<br />sub v s (<span class="disFm">Dis</span> p q) <span class=\"eqdef\">=</span> <span class="disFm">Dis</span> (sub v s p) (sub v s q)<br />sub v s (<span class="conFm">Con</span> p q) <span class=\"eqdef\">=</span> <span class="conFm">Con</span> (sub v s p) (sub v s q)<br />sub v s (<span class="exiFm">Exi</span> p) <span class=\"eqdef\">=</span> <span class="exiFm">Exi</span> (sub (v + 1) (inc_term s) p)<br />sub v s (<span class="uniFm">Uni</span> p) <span class=\"eqdef\">=</span> <span class="uniFm">Uni</span> (sub (v + 1) (inc_term s) p)</div>'));

    // Hide tabs default
    helpContent.children().hide();

    //
    helpContent.append(dssContent);
    helpContent.append(sorContent);
    helpContent.append(sampleContent);
    helpContent.append(isabelleContent);

    helpContent.children().hide();

    overlay.append(content);

    // Apply button events

    // Hide visible tabs on click
    $(".btnLeft, .btnMid, .btnRight").children().on("click", () => {
        $(".btnMid").children().removeClass("buttonMidHover");
        $(".btnRight").children().removeClass("buttonRightHover");

        helpContent.children(":visible").hide();
    });

    $(".btnMid").children().on("click", e => $(e.currentTarget).addClass("buttonMidHover"));
    $(".btnRight").children().on("click", e => $(e.currentTarget).addClass("buttonRightHover"));

    // Show corresponding tab on click
    isaFileButton.on("click", (e) => {
        isabelleContent.show();
    })

    folButton.on("click", () => {
        dssContent.show();
    });

    ndButton.on("click", () => {
        sorContent.show();
    });

    sampleButton.click(() => {
        sampleContent.show();
    });

    cancel.click(e => {
        $(".closeCenteredOverlay", overlay).trigger("click");
    });

    ndButton.trigger("click");
};

function htmlEncodeIsabelle(s: string): string {
    return s
        .replace(/\\/g, "&#92;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
}

function verifyInner(overlay: JQuery, callback: () => void): void {
    // Flexible content
    var content = $("<div class=\"flexContentY\"></div>");
    overlay.append(content);

    // Make menu buttons
    var buttonsContainer = $("<div class=\"buttonContainer\"></div>");
    var buttonsTable = $("<div class=\"buttonsTable\"></div>");
    var buttonsRow = $("<div class=\"buttonsRow\"></div>");

    var btnLeft = $('<div class="btnLeft"></div>');
    var btnMid = $('<div class="btnMid"></div>');
    var btnRight = $('<div class="btnRight"></div>');

    buttonsRow.append(btnLeft);
    buttonsRow.append(btnMid);
    buttonsRow.append(btnRight);

    buttonsContainer.append(buttonsTable);
    buttonsTable.append(buttonsRow);

    var cancel = $('<div class="button small">Cancel verify</div>');
    var verButton = $('<div class="button small">NaDeA, soundness and completeness</div>');
    var nadButton = $('<div class="button small">Base theory - Natural_Deduction_Assistant.thy</div>');
    var openButton = $('<div class="button small">Open formulas - Scratch.thy</div>');
    var isaButton = $('<div class="button small">Verify natural deduction proof in Isabelle</div>');

    btnLeft.append(cancel);
    btnMid.append(verButton);
    btnMid.append(nadButton);
    btnMid.append(openButton);
    btnRight.append(isaButton);

    content.append(buttonsContainer);

    // Content box
    var verifyContent = $('<div class="helpContent"></div>');
    content.append(verifyContent);

    // Tabs
    /* Content: Isabelle */
    var isabelleContent = $('<div></div>');

    /* Content: */
    var openContent = $('<div class="verifyTextareaContainer"></div>');

    var verContent = $(
        '<div>' +
        '<div class="textline extraSpace">NaDeA, this browser application, is not formally verified. This means that, though unlikely, it may be possible to produce proofs of invalid formulas. Conversely there might exist valid formulas that one cannot prove in NaDeA. These shortcomings are addressed as follows.</div>' +

        '<div class="textline"><strong>Soundness</strong></div>' +
        '<div class="textline">As explained in the <span style="color: green">Code</span> window, the first-order logic used in NaDeA has a formal syntax and semantics encoded in Isabelle. The proof rules available in the browser are also encoded in Isabelle. Under <span style="color: green">Code</span> a formally verified soundness theorem is available that connects the semantics with these proof rules. The soundness theorem states that if a natural deduction proof of a formula can be derived then the formula is valid.</div>' +
        '<div class="textline extraSpace">The <span style="color: blue">blue tab</span> in the top right corner translates a finished NaDeA proof into the corresponding Isabelle-embedded proof. Furthermore it uses the soundness theorem to prove its validity. To verify a proof produced in NaDeA, this Isabelle code can be copied and pasted into the end of the NaDeA.thy file. Thus it is easy to check the correctness of a proof.</div>' +

        '<div class="textline"><strong>Completeness</strong></div>' +
        '<div class="textline">The <span style="color: green">Base theory</span> tab above includes an Isabelle theory with a soundness and completeness theorem.</div>' +
        '<div class="textline">The completeness theorem states that any valid formula can be proved by the proof rules.</div>' +
        '<div class="textline">Thus in the unlikely case that a proof of a valid formula cannot be completed in NaDeA, the proof can be made directly in the Isabelle encoding instead, where the completeness theorem guarantees that the proof is possible if the formula is valid.</div>' +
        '<div class="textline extraSpace">The theory uses Isabelle\'s full syntax, not just the ASCII-subset, and is best viewed by downloading it and loading it in Isabelle.</div>' +
        '<div class="textline">To obtain a proof of the validity of an "opened" formula given a proof of a closed version of it, the tab <span style="color:green">Open formulas</span> can be used. The generated Isabelle theory there imports the base theory and verifies the validity of the original formula as well as the validity of all versions of it with some number of outer universal quantifiers omitted.</div>' +
        '<div class="textline">This theory should be saved in the same folder as the base theory.</div>' +
        '</div>');

    var nadContent = $('<div class="verifyTextareaContainer"></div>');

    nadContent.append('<textarea class="verifyTextarea" spellcheck="false" readonly="true">'
        + naturalDeductionAssistantThy + '</textarea>');

    var open = "theory Scratch imports Natural_Deduction_Assistant begin\n\n";

    var waiting = currentState.p.waiting();

    if ((countUnknowns(currentState.p.goal) + waiting) == 0) {
        var w: Worker = new Worker("verify_worker.js");

        if (countUnknowns(currentState.p) == 0) {
            var proof = encodeProof(currentState.p);

            w.onmessage = e => {
                var code = '(* Insert before "end" in NaDeA.thy or other suitable Isabelle theory file *)\n\n';
                var isabelleLines = formatIsabelle(e.data.isabelleAscii);
                var proofLines = formatIsabelle(e.data.proof);

                code += isabelleLines.join("\n");
                code += "\n\n";
                code += proofLines.join("\n");

                isabelleContent.append('<pre class="isabelleFileView">' + code + '</pre>');

                open += e.data.isabelle + "\n\n";
                open += e.data.open + "\n";
                open += "end\n";
                openContent.append('<textarea class="verifyTextarea" spellcheck="false">' + open + '</textarea>');
            }

            w.postMessage({ proof: proof });
        } else {
            var goal = encodeProof(currentState.p.goal);

            console.log(goal);

            w.onmessage = e => {
                open += e.data.isabelle + "\n\n";
                open += "(* Finish the proof to complete this verification. *)\n\n"
                open += "end\n";
                openContent.append('<textarea class="verifyTextarea" spellcheck="false" readonly="true">' + open + '</textarea>');

            }

            w.postMessage({ goal: goal });

            isabelleContent.append('<p>Please finish your proof before verifying it.</p>');
        }
    } else {
        isabelleContent.append('<p>Please finish your proof before verifying it.</p>');

        open += "(* Please finish your proof before verifying it. *)\n\n"
        open += "end\n";
        openContent.append('<textarea class="verifyTextarea" spellcheck="false">' + open + '</textarea>');

    }

    // Hide tabs default
    verifyContent.children().hide();

    verifyContent.append(openContent);
    verifyContent.append(verContent);
    verifyContent.append(nadContent);
    verifyContent.append(isabelleContent);

    verifyContent.children().hide();

    overlay.append(content);

    // Apply button events

    // Hide visible tabs on click
    $(".btnLeft, .btnMid, .btnRight").children().on("click", () => {
        $(".btnMid").children().removeClass("buttonMidHover");
        $(".btnRight").children().removeClass("buttonRightHover");

        verifyContent.children(":visible").hide();
    });

    $(".btnMid").children().on("click", e => $(e.currentTarget).addClass("buttonMidHover"));
    $(".btnRight").children().on("click", e => $(e.currentTarget).addClass("buttonRightHover"));

    // Show corresponding tab on click
    isaButton.on("click", (e) => {
        isabelleContent.show();
    })

    nadButton.on("click", () => {
        nadContent.show();
    });

    openButton.on("click", () => {
        openContent.show();
    });

    verButton.on("click", () => {
        verContent.show();
    });

    cancel.click(e => {
        $(".closeCenteredOverlay", overlay).trigger("click");
    });

    verButton.trigger("click");
};

var testHintData: { testGoal: Formula, hintGoal: Formula, testComments: string[], hints: string[][], hintsUsed: number }[] = [];

function setupExerciseAndHintData() {
    var regexHintDelimiter = /\.\.\./;

    // Setup data
    for (var i = 0; i <= 9; i++) {
        testHintData[i] = { testGoal: undefined, hintGoal: undefined, testComments: null, hints: [], hintsUsed: 0 };

        var testX = proofCodes["Test " + i];
        var hintX = proofCodes["Hint " + i];

        var regex = /^\..*$/m;

        if (testX !== undefined) {
            var testXFinal = testX.split("\n").filter(v => { return regex.exec(v) === null; }).shift();
            testHintData[i].testComments = testX.split("\n").filter(v => { return regex.exec(v) !== null; }).map(v => {
                return v.substring(2);
            });
            var testXDecoded = decodeProof(testXFinal);

            if (testXDecoded === null) {
                console.log("Test " + i + " could not be decoded. Something went very wrong...");
            }

            if (testXDecoded.length > 0) {
                testHintData[i].testGoal = testXDecoded[0].goal;
            }
        }

        if (hintX !== undefined) {
            var hintXFinal = hintX.split("\n").filter(v => { return regex.exec(v) === null; }).shift();
            var hintXDecoded = decodeProof(hintXFinal);

            var hintIndex = 0;

            var hintXComments = hintX.split("\n").filter(v => { return regex.exec(v) !== null; }).forEach(v => {
                if (v.search(regexHintDelimiter) > -1) {
                    hintIndex++;
                    testHintData[i].hints[hintIndex] = [];
                } else {
                    if (testHintData[i].hints.length <= hintIndex)
                        testHintData[i].hints[hintIndex] = [];

                    testHintData[i].hints[hintIndex].push(v.substring(2));
                }
            });

            if (hintXDecoded === null) {
                console.log("Test " + i + " could not be decoded. Something went very wrong...");
            }

            if (hintXDecoded.length > 0) {
                testHintData[i].hintGoal = hintXDecoded[0].goal;
            }
        }
    }

    if (exsContent !== undefined)
        updateExerciseAndHintContent();


}

var exsContent: JQuery;
var hintContent: JQuery[];

function updateExerciseAndHintContent() {
    // Exercise table
    var exerciseTableRows = "";

    for (var i = 0; i <= 9; i++) {
        exerciseTableRows += '<div class="tableRow">';

        if (testHintData[i] === undefined || testHintData[i].testGoal === undefined) {
            exerciseTableRows += '<div class="tableCell alignRight">-</div>';
        } else if (testHintData[i].testGoal === null) {
            exerciseTableRows += '<div class="tableCell alignRight"><span class="formalUnknown">¤</span></div>';
        } else {
            exerciseTableRows += '<div class="tableCell alignRight formal">' + getFormalSyntax(testHintData[i].testGoal, 0, null, [testHintData[i].testGoal]) + '</div>';
        }

        exerciseTableRows += '<div class="tableCell">' + i + '</div>';

        if (testHintData[i] === undefined || testHintData[i].hintGoal === undefined) {
            exerciseTableRows += '<div class="tableCell">-</div>';
        } else if (testHintData[i].hintGoal === null) {
            exerciseTableRows += '<div class="tableCell"><span class="formalUnknown">¤</span></div>';
        } else {
            exerciseTableRows += '<div class="tableCell formal">' + getFormalSyntax(testHintData[i].hintGoal, 0, null, [testHintData[i].hintGoal]) + '</div>';
        }

        exerciseTableRows += '</div>';
    }

    var exsContentStr = '<div class="table">'
        + '<div class="tableRow borderBottom">'
        + '<div class="tableCell alignRight"><strong>Test</strong></div>'
        + '<div class="tableCell"><strong>#</strong></div>'
        + '<div class="tableCell"><strong>Hint</strong></div>'
        + '</div>'
        + exerciseTableRows
        + '</div>';

    exsContent.children("#exsContent").html(exsContentStr);

    // Hint page 0-9
    var updateHintPage = i => {
        if (testHintData[i] !== undefined) {
            if (testHintData[i].hintGoal === undefined) {
                $(".hintStarContainer", hintContent[i]).remove();
            } else {
                var hscHtml: string = "";
                for (var j = 0; j < testHintData[i].hints.length + 1 - testHintData[i].hintsUsed; j++)
                    hscHtml += '&#9733;';
                for (var j = 0; j < testHintData[i].hintsUsed; j++)
                    hscHtml += '&#9734;';

                $(".hintStarContainer", hintContent[i]).html(hscHtml);
            }

            $("div", hintContent[i]).each((j, e) => {
                var ithHint: number = +$(e).data("ithHint");

                if (ithHint === undefined)
                    return true;

                if (ithHint > testHintData[i].hintsUsed)
                    $(e).hide();
                else
                    $(e).show();
            });
        }
    };

    for (var i = 0; i <= 9; i++) {
        var hs = "";
        if (testHintData[i] === undefined) {
            hs += '<div class="textline">Hint ' + i + ' could not be found.</div>';
        } else {
            hs += '<div class="formal textline extraSpace">It is recommended that another browser tab is used to examine following test example (use the load window).</div>';
            hs += '<div class="formal textline lessSpace"><strong>Test ' + i + '</strong>: ';
            hs += (testHintData[i].testGoal === undefined) ? "-" : getFormalSyntax(testHintData[i].testGoal, 0, null, [testHintData[i].testGoal]);
            hs += '</div>';

            testHintData[i].testComments.forEach((l, j) => {
                hs += '<div class="textline' + (j == testHintData[i].testComments.length - 1 ? ' extraSpace' : '') + '">' + l + '</div>';
            });

            hs += '<div class="formal textline extraSpace">It is recommended that another browser tab is used to solve following exercise (click on the stars to get the next hint part).</div>';
            hs += '<div class="formal textline lessSpace floatLeft"><strong>Hint ' + i + '</strong>: ';
            hs += (testHintData[i].hintGoal === undefined) ? "-" : getFormalSyntax(testHintData[i].hintGoal, 0, null, [testHintData[i].hintGoal]);
            hs += '</div>';

            hs += '<div class="floatRight hintStarContainer" id="hintStarContainer' + i + '"></div>';

            hs += '<div class="clear hintContainer">';
            testHintData[i].hints.forEach((hintsX, k) => {
                hintsX.forEach((h, j) => {
                    hs += '<div class="textline" data-ith-hint="' + (k + 1) + '">' + h + '</div>';
                });
            });

            hs += '<div class="textline" data-ith-hint="' + (testHintData[i].hints.length + 1) + '">See the proof at https://nadea.compute.dtu.dk/#' + i + '</div>';

            hs += '</div>';
        }

        hintContent[i].html(hs);

        updateHintPage(i);

        if (testHintData[i] !== undefined) {
            if (testHintData[i].hintsUsed <= testHintData[i].hints.length) {
                $(document).off("click", "#hintStarContainer" + i);
                $(document).on("click", "#hintStarContainer" + i, { hintNumber: i }, e => {
                    testHintData[e.data.hintNumber].hintsUsed++;
                    updateHintPage(e.data.hintNumber);

                    if (testHintData[e.data.hintNumber].hintsUsed == testHintData[e.data.hintNumber].hints.length + 1) {
                        $(document).off("click", "#hintStarContainer" + e.data.hintNumber);

                        $(e.currentTarget).addClass("allUsed");
                    }
                });
            } else {
                $("#hintStarContainer" + i).addClass("allUsed");
            }
        }
    }
}

function helpInner(overlay: JQuery, callback: () => void): void {
    // Flexible content
    var content = $("<div class=\"flexContentY\"></div>");
    overlay.append(content);

    // Make menu buttons
    var buttonsContainer = $("<div class=\"buttonContainer\"></div>");
    var buttonsTable = $("<div class=\"buttonsTable\"></div>");
    var buttonsRow = $("<div class=\"buttonsRow\"></div>");

    var btnLeft = $('<div class="btnLeft"></div>');
    var btnMid = $('<div class="btnMid"></div>');
    var btnRight = $('<div class="btnRight"></div>');

    buttonsRow.append(btnLeft);
    buttonsRow.append(btnMid);
    buttonsRow.append(btnRight);

    buttonsContainer.append(buttonsTable);
    buttonsTable.append(buttonsRow);

    // Buttons
    var cancel = $('<div class="button small">Cancel help</div>');
    var welcomeButton = $('<div class="button small">Welcome</div>');
    var tutorialButton = $('<div class="button small">Tutorial</div>');
    var exsButton = $('<div class="button small">Exercises</div>');
    var pbsButton = $('<div class="button small">Publications</div>');
    var aboutButton = $('<div class="button small">About NaDeA ' + versionNumber + '</div>');

    btnLeft.append(cancel);

    var hintsButtonJQuery: JQuery[] = [];

    btnMid.append(welcomeButton);
    btnMid.append(tutorialButton);
    btnMid.append(exsButton);

    for (var i = 0; i <= 9; i++) {
        hintsButtonJQuery[i] = $('<div class="button small hint">Hint ' + i + '</div>');
        hintsButtonJQuery[i].data("ithHint", i);

        btnMid.append(hintsButtonJQuery[i]);
    }

    btnMid.append(pbsButton);

    btnRight.append(aboutButton);

    content.append(buttonsContainer);

    // Content box
    var helpContent = $('<div class="helpContent"></div>');
    content.append(helpContent);

    // Tabs
    /* Content: Welcome */
    var welcomeContent = $('<div><div class="headline">Welcome to NaDeA: A Natural Deduction Assistant with a Formalization in Isabelle</div><div class="textline extraSpace">NaDeA runs in a standard browser - preferably in full screen - and is open source software - please find the source code and further information here: https://logic-tools.github.io/ </div>'
        + '<div class="textline extraSpace">Use Tabs in your browser as necessary.</div>'
        + '<div class="textline extraSpace">The following three buttons are available in the main proof window (the Escape key can always be pressed to cancel and go to the main proof window).</div>'
        + '<div class="columnContainer extraSpace">'
        + '<div class="column3"><div class="buttonStaticContainer"><div class="loadStatic buttonStatic big">Load</div></div><div class="textline">The Load button brings up the load window which allows for simple import/export of proof lines.</div>'
        + '<div class="textline">Also a number of so-called tests can be loaded as explained in the help window (see Exercises).</div></div>'
        + '<div class="column3"><div class="buttonStaticContainer"><div class="codeStatic buttonStatic big">Code</div></div><div class="textline">The Code button brings up the code window with the Isabelle formalization code for natural deduction as explained in the help window (see Tutorial).</div>'
        + '<div class="textline">Also the complete Isabelle theory file with comments is available.</div></div>'
        + '<div class="column3"><div class="buttonStaticContainer"><div class="helpStatic buttonStatic big">Help</div></div><div class="textline">The Help button brings up the help window with this welcome information and a number of so-called hints.</div>'
        + '<div class="textline">After this welcome information then please click on Tutorial and thereafter continue with Exercises…</div></div>'
        + '<div class="clear"></div>'
        + '</div>'
        + '<div class="textline extraSpace">In order to edit a proof, edit mode must be turned on (by default the edit mode is turned off). Edit mode can be toggled by clicking anywhere in the main proof window below the header.</div>'
        + '<div class="textline lessSpace">In order to undo a step, click the Undo button (or Delete key). All previous proof states can be reached.</div>'
        + '<div class="textline extraSpace">By clicking the Stop button (or Insert key), the undo sequence (performed up until Stop) becomes available for undoing such that the steps undone can be reached once more.</div>'
        + '<div class="textline lessSpace">To the left of the Stop button there are two numbers "x/y":</div>'
        + '<div class="textline extraSpace">x marks the position of the current state on the Undo stack. y is the total number of states on the stack which can all be reached by consecutive clicks on Undo.</div>'
        + '<div class="buttonStaticContainer"><div class="verifyStatic buttonStatic big">1</div></div>'
        + '<div class="textline lessSpace">The verification button represents the number of <span style="color: red;">¤</span> symbols in the current proof state (the number 1 in the above button). If (and only if) this becomes 0, the proof is finished.</div>'
        + '<div class="textline extraSpace">When this is the case, the button may be clicked to verify the proof in Isabelle. It may also be clicked at any other time to read about the completeness of NaDeA.</div>'
        + '<div class="textline">Please provide feedback to Associate Professor Jørgen Villadsen, DTU Compute, Denmark: https://people.compute.dtu.dk/jovi/ </div></div>');

    var tutorialContent = $('<div>'
        + '<div class="columnContainer">'
        + '<div class="column2">'
        + '<div class="codeBlock"><div class="textline"><strong>Getting Started</strong></div><div class="textline">1. To build the sample formula A &rarr; A start by turning on edit mode and clicking <span style="color: red;">¤</span>. The square brackets <div class="leftBracket">[</div><div class="rightBracket">]</div> denote the current list of assumptions which is initially empty. Use a predicate A with no arguments.</div><div class="textline">2. After building the sample formula, apply the rule Imp_I (Implication-Introduction) to prove the formula A by assumption of A. The rule is also selected by clicking <span style="color: red;">¤</span>.</div><div class="textline">3. The proof finishes automatically by applying the rule Assume since the formula A is found in the list of assumptions. It is finished because there is no pending <span style="color: red;">¤</span>.</div></div>'
        + '<div class="clear extraSpace"></div>'
        + '<div class="buttonStaticContainer"><div class="proofjudgeBtnStatic buttonStatic big">ProofJudge</div></div>'
        + '<div class="codeBlock"><div class="textline"><strong>ProofJudge</strong></div>'
        + '<div class="textline">There are two components to ProofJudge:</div>'
        + '<div class="textline">1. The first component judges proofs while they are being developed. If a (sub)goal cannot be proved, its line number will turn orange like this <span style="color: orange">1</span>. You can try this out by trying to prove Falsity and waiting half a second for the goal to be checked.</div>'
        + '<div class="texline">2. The second component requires affiliation with a course and logging in by clicking the ProofJudge button shown above. Exercises in the course are available there and proofs can be handed in as answers to these. Furthermore proofs can be named and saved as drafts for later work.</div>'
        + '</div></div>'
        + '<div class="column2">'
        + '<div class="codeBlock"><div class="textline"><strong>Natural Deduction Primitives</strong></div><div class="textline">OK p a: The formula p follows from the assumptions a.</div><div class="textline">news c l: True if the identifier c does not occur in the list of formulas l.</div><div class="textline">sub n t p: Returns the formula p where the term t has been substituted for the variable with the de Bruijn index n.</div></div>'
        + '<div class="clear"></div>'
        + '</div>'
        + '</div>');

    /* Content: Exercises */
    exsContent = $('<div>' +
        '<div class="textline extraSpace">A test resumes from the last proof state but a hint replays from the first proof state (click Undo to show the proof states).</div>' +
        '<div id="exsContent" class="extraSpace"></div>' +
        '<div class="textline extraSpace">Exercises are available as Hint 0-9 in this Help window and sample proofs are available as Test 0-9 in the Load window.</div>' +
        '<div class="textline extraSpace">Tabs in the browser are useful to switch between the load window, the code window, the help windows and the main proof window.</div>' +
        '<div class="textline">NaDeA starts with a hint if the hash mark # and the hint number is added to the address in the browser address line.</div>' +
        '</div>');

    /* Content: Publications */
    var pbsContent = $('<div>' +
        '<div class="textline"><i>NaDeA: A Natural Deduction Assistant with a Formalization in Isabelle</i></div>' +
        '<div class="textline">Jørgen Villadsen, Alexander Birch Jensen & Anders Schlichtkrull</div>' +
        '<div class="textline">IFCoLog Journal of Logics and their Applications 4(1) p. 55-82 2017</div>' +
        '<div class="textline medSpace">http://www.collegepublications.co.uk/journals/ifcolog/</div>' +
        '<div class="textline">A preliminary version appeared in Proceedings of 4th International Conference on Tools for Teaching Logic, Rennes, France, p. 253-262 2015</div>' +
        '<div class="textline extraSpace">http://arxiv.org/abs/1507.04002</div>' +
        '<div class="textline"><i>ProofJudge: Automated Proof Judging Tool for Learning Mathematical Logic</i></div>' +
        '<div class="textline">Jørgen Villadsen</div>' +
        '<div class="textline medspace">Proceedings of the Exploring Teaching for Active Learning in Engineering Education Conference, Copenhagen, Denmark, p. 39-44 2015</div>' +
        '<div class="textline extraSpace">http://etalee2015.etalee.dk/</div>' +
        '<div class="textline"><i>Natural Deduction and the Isabelle Proof Assistant</i></div>' +
        '<div class="textline">Jørgen Villadsen, Andreas Halkjær From & Anders Schlichtkrull</div>' +
        '<div class="textline">Draft</div>' +
        '</div>');

    /* Content: About NaDeA */
    var aboutContent = $('<div><div class="textline extraSpace"><strong>Supported by a DTU E-learning Grant, DTU Compute\'s Strategic Foundation & Algorithms, Logic and Graphs Section</strong></div><div class="codeBlock"><div class="textline"><strong>Copyright Notice and Disclaimer</strong></div><div class="codeBlock extraSpace">Copyright &copy; 2015-2018 Jørgen Villadsen, Andreas Halkjær From, Alexander Birch Jensen &amp; Anders Schlichtkrull<br /><br />Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:<br /><br />The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.<br /><br />THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.</div></div>'
        + '<div class="codeBlock">'
        + '<div class="textline"><strong>Acknowledgements</strong></div>'
        + '<div class="codeBlock">Based on:</br>Stefan Berghofer: First-Order Logic According to Fitting. Archive of Formal Proofs 2007. https://www.isa-afp.org/entries/FOL-Fitting.shtml</div>'
        + '</div></div>');

    // Hide tabs default
    helpContent.children().hide();

    //
    helpContent.append(welcomeContent);
    helpContent.append(tutorialContent);
    helpContent.append(exsContent);
    helpContent.append(pbsContent);

    hintContent = [];
    hintsButtonJQuery.forEach((e, i) => {
        hintContent[i] = $('<div id="hint' + e.data("ithHint") + '"></div>')
        helpContent.append(hintContent[i]);
    });

    helpContent.append(aboutContent);

    helpContent.children().hide();

    overlay.append(content);

    // Apply button events

    // Hide visible tabs on click
    $(".btnLeft, .btnMid, .btnRight").children().on("click", () => {
        $(".btnMid").children().removeClass("buttonMidHover");
        $(".btnRight").children().removeClass("buttonRightHover");

        helpContent.children(":visible").hide();
    });

    $(".btnMid").children().on("click", e => $(e.currentTarget).addClass("buttonMidHover"));
    $(".btnRight").children().on("click", e => $(e.currentTarget).addClass("buttonRightHover"));

    // Show corresponding tab on click
    welcomeButton.on("click", (e) => {
        welcomeContent.show();
    })

    tutorialButton.on("click", (e) => {
        tutorialContent.show();
    })

    exsButton.on("click", () => {
        exsContent.show();
    });

    pbsButton.on("click", () => {
        pbsContent.show();
    });

    aboutButton.on("click", () => {
        aboutContent.show();
    });

    cancel.click(e => {
        $(".closeCenteredOverlay", overlay).trigger("click");
    });

    hintsButtonJQuery.forEach(e => {
        e.on("click", () => {
            $("#hint" + e.data("ithHint")).show();
        });
    });

    updateExerciseAndHintContent();

    welcomeButton.trigger("click");
};

/// <reference path="references.d.ts"/>

/*
 * Term classes
 */

class Term {
    getInternalName(): string {
        return Term.getInternalName();
    }

    static getInternalName(): string {
        return "Term";
    }

    getIsabelleTerm(nq: number): string {
        throw new Error("Should not be called from abstract class");
    }
}

class tmVar extends Term {
    nat: number;

    constructor(nat: number) {
        super();

        nat = +nat;

        if (nat < 0)
            throw new RangeError();

        this.nat = nat;
    }

    getInternalName(): string {
        return tmVar.getInternalName();
    }

    static getInternalName(): string {
        return "Var";
    }

    getIsabelleTerm(nq: number): string {
        return getQuantifiedVariable(nq + this.nat, true);
    }
}

class tmFun extends Term {
    id: string;
    tms: Term[];

    constructor(id: string, tms: Term[]) {
        super();

        this.id = id;
        this.tms = tms;
    }

    getInternalName(): string {
        return tmFun.getInternalName();
    }

    static getInternalName(): string {
        return "Fun";
    }

    getIsabelleFormula(nq: number): string {
        var isaFm = this.id;

        if (this.tms.length > 0) {
            isaFm += "(";
            isaFm += this.tms.map(t => { return t.getIsabelleTerm(nq) }).join(", ");
            isaFm += ")";
        }

        return isaFm;
    }
}

/*
 * Formula classes
 */

class Formula {
    getInternalName(): string {
        return Formula.getInternalName();
    }

    static getInternalName(): string {
        return "Formula";
    }

    getIsabelleFormula(nq: number): string {
        throw new Error("Should not be called from abstract class");
    }
}

class FormulaOneArg extends Formula {
    fm: Formula;

    constructor(fm: Formula) {
        super();
        this.fm = fm;
    }

    getIsabelleFormula(nq: number): string {
        throw new Error("Should not be called from abstract class");
    }
}

class FormulaTwoArg extends Formula {
    lhs: Formula;
    rhs: Formula;

    constructor(lhs: Formula, rhs: Formula) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }

    getIsabelleFormula(nq: number): string {
        throw new Error("Should not be called from abstract class");
    }
}

class fmFalsity extends Formula {

    constructor() {
        super();
    }

    getInternalName(): string {
        return fmFalsity.getInternalName();
    }

    static getInternalName(): string {
        return "Falsity";
    }

    getIsabelleFormula(nq: number): string {
        return "False";
    }
};

class fmPre extends Formula {
    id: string;
    tms: Term[];

    constructor(id: string, tms: Term[]) {
        super();

        this.id = id;
        this.tms = tms;
    }

    getInternalName(): string {
        return fmPre.getInternalName();
    }

    static getInternalName(): string {
        return "Pre";
    }

    getIsabelleFormula(nq: number): string {
        var isaFm = this.id;

        if (this.tms.length > 0) {
            isaFm += "(";
            isaFm += this.tms.map(t => { return t.getIsabelleTerm(nq) }).join(", ");
            isaFm += ")";
        }

        return isaFm;
    }
}

class fmImp extends FormulaTwoArg {
    constructor(lhs: Formula, rhs: Formula) {
        super(lhs, rhs);
    }

    getInternalName(): string {
        return fmImp.getInternalName();
    }

    static getInternalName(): string {
        return "Imp";
    }

    getIsabelleFormula(nq: number): string {
        return "(" + this.lhs.getIsabelleFormula(nq) + " \<longrightarrow> " + this.rhs.getIsabelleFormula(nq) + ")";
    }
}

class fmDis extends FormulaTwoArg {
    constructor(lhs: Formula, rhs: Formula) {
        super(lhs, rhs);
    }

    getInternalName(): string {
        return fmDis.getInternalName();
    }

    static getInternalName(): string {
        return "Dis";
    }

    getIsabelleFormula(nq: number): string {
        return "(" + this.lhs.getIsabelleFormula(nq) + " \<or> " + this.rhs.getIsabelleFormula(nq) + ")";
    }
}

class fmCon extends FormulaTwoArg {
    constructor(lhs: Formula, rhs: Formula) {
        super(lhs, rhs);
    }

    getInternalName(): string {
        return fmCon.getInternalName();
    }

    static getInternalName(): string {
        return "Con";
    }

    getIsabelleFormula(nq: number): string {
        return "(" + this.lhs.getIsabelleFormula(nq) + " \<and> " + this.rhs.getIsabelleFormula(nq) + ")";
    }
}

class fmExi extends FormulaOneArg {
    constructor(fm: Formula) {
        super(fm);
    }

    getInternalName(): string {
        return fmExi.getInternalName();
    }

    static getInternalName(): string {
        return "Exi";
    }

    getIsabelleFormula(nq: number): string {
        return "(\<exists>" + getQuantifiedVariable(nq, true) + ". " + this.fm.getIsabelleFormula(nq + 1) + ")";
    }
}

class fmUni extends FormulaOneArg {
    constructor(fm: Formula) {
        super(fm);
    }

    getInternalName(): string {
        return fmUni.getInternalName();
    }

    static getInternalName(): string {
        return "Uni";
    }

    getIsabelleFormula(nq: number): string {
        return "(\<forall>" + getQuantifiedVariable(nq, true) + ". " + this.fm.getIsabelleFormula(nq + 1) + ")";
    }
}

interface InductiveInterface {
    evaluate(): void;
    isApplicable(): boolean;
    getPremisesAux(input: any[]): void;
}

class Inductive implements InductiveInterface {
    goal: Formula;
    premises: Inductive[] = [];
    assumptions: Formula[] = [];
    trueByAssumption: boolean;

    constructor(goal: Formula, assumptions: Formula[]) {
        this.goal = goal;
        this.assumptions = assumptions;

        this.checkGoal();
    }

    getPremises(...input): Inductive[] {
        if (typeof this.goal === undefined) {
            throw new Error("Must define a goal to infer premises");
        }

        if (!this.isApplicable())
            throw new Error("The rule is not applicable to this goal");

        this.premises = [];

        this.getPremisesAux(input);

        return this.premises;
    }

    checkGoal(): void {
        this.trueByAssumption = false;

        if (formulaContainsUnknowns(this.goal) || this.assumptions.some(v => { return formulaContainsUnknowns(v) }))
            return;

        for (var i in this.assumptions)
            if (equalFormulas(this.assumptions[i], this.goal)) {
                this.trueByAssumption = true;
                return;
            }
    }

    evaluate(): void {
        throw new Error("Method is abstract and must be overloaded");
    }

    getPremisesAux(input: any[]): void {
        throw new Error("Method is abstract and must be overloaded");
    }

    isApplicable(): boolean {
        throw new Error("Method is abstract and must be overloaded");
    }

    inferTruthValue(): void {
        this.evaluate();
    }

    inferTruthValueAux(n: number) {
        if (this.premises.length < n)
            throw new Error("Premises not sufficiently instantiated");

        var tv: boolean = true;

        for (var i = 0; i < n; i++) {
            if (this.premises[i].trueByAssumption === false) {
                tv = false;
                break;
            }
        }

        this.trueByAssumption = tv;
    }

    getInternalName(): string {
        return Inductive.getInternalName();
    }

    static getInternalName(): string {
        return "OK";
    }

    getIsabelleProof(indent: number): string {
        throw new Error("Method is abstract and must be overloaded");
    }

    waiting(): number {
        return this.premises.reduce((acc, p) => acc + p.waiting(), 0);
    }
}

class synBool extends Inductive implements InductiveInterface {

    constructor(goal: Formula, assumptions: Formula[]) {
        super(goal, assumptions);

        if (!this.isApplicable()) {
            throw new Error("Could not apply rule (synBool) to formula:\n" + getInternalSyntaxHTML(goal));
        }
    }

    evaluate() {
        this.inferTruthValueAux(1);
    }

    isApplicable() {
        return true;
    }

    static isApplicable(goal) {
        return true;
    }

    getPremisesAux(input: Formula[]) {
        var falsity: Formula = new fmFalsity();

        var assumptions: Formula[] = copyAssumptions(this).as;

        assumptions.unshift(new fmImp(this.goal, falsity));

        var inductive: Inductive = new Inductive(falsity, assumptions);
        this.premises.push(inductive);
    }

    getInternalName(): string {
        return synBool.getInternalName();
    }

    static getInternalName(): string {
        return "Boole";
    }

    getIsabelleProof(indent: number): string {
        var prepend = Array(indent).join("\t");
        //
        return "sorry";
    }
}

class synImpE extends Inductive implements InductiveInterface {

    constructor(goal: Formula, assumptions: Formula[]) {
        super(goal, assumptions);

        if (!this.isApplicable()) {
            throw new Error("Could not apply rule (synImpE) to formula:\n" + getInternalSyntaxHTML(goal));
        }
    }

    evaluate() {
        this.inferTruthValueAux(2);
    }

    isApplicable() {
        return true;
    }

    static isApplicable(goal) {
        return true;
    }

    getPremisesAux(input: Formula[]) {
        if (input.length < 1) {
            throw new Error("Expecting formula q");
        }

        var p: Formula = input[0];
        var fm1: Formula = new fmImp(p, this.goal);

        var assumptions: Formula[] = copyAssumptions(this).as;

        var inductive1: Inductive = new Inductive(fm1, assumptions);
        var inductive2: Inductive = new Inductive(p, assumptions);
        this.premises.push(inductive1);
        this.premises.push(inductive2);
    }

    getInternalName(): string {
        return synImpE.getInternalName();
    }

    static getInternalName(): string {
        return "ImpE";
    }

    getIsabelleProof(indent: number): string {
        var prepend = Array(indent).join("\t");

        var isaCode: string;



        return isaCode;
    }
}

class synImpI extends Inductive implements InductiveInterface {

    constructor(goal: Formula, assumptions: Formula[]) {
        super(goal, assumptions);

        if (!this.isApplicable()) {
            throw new Error("Could not apply rule (synImpI) to formula:\n" + getInternalSyntaxHTML(goal));
        }
    }

    evaluate() {
        this.inferTruthValueAux(1);
    }

    isApplicable() {
        return synImpI.isApplicable(this.goal);
    }

    static isApplicable(goal) {
        return goal instanceof fmImp;
    }

    getPremisesAux(input: Formula[]) {
        var p: Formula = copyFormula((<fmImp>this.goal).lhs);
        var q: Formula = copyFormula((<fmImp>this.goal).rhs);

        var assumptions: Formula[] = copyAssumptions(this).as;
        assumptions.unshift(p);

        var inductive = new Inductive(q, assumptions);
        this.premises.push(inductive);
    }

    getInternalName(): string {
        return synImpI.getInternalName();
    }

    static getInternalName(): string {
        return "ImpI";
    }

    getIsabelleProof(indent: number): string {
        var prepend = Array(indent).join("\t");
        //
        return "sorry";
    }
}

class synDisE extends Inductive implements InductiveInterface {

    constructor(goal: Formula, assumptions: Formula[]) {
        super(goal, assumptions);

        if (!this.isApplicable()) {
            throw new Error("Could not apply rule (synDisE) to formula:\n" + getInternalSyntaxHTML(goal));
        }
    }

    evaluate() {
        this.inferTruthValueAux(3);
    }

    isApplicable() {
        return true;
    }

    static isApplicable(goal) {
        return true;
    }

    getPremisesAux(input: Formula[]) {
        if (input.length < 2) {
            throw new Error("Expecting formulas p and q");
        }

        var p: Formula = input[0];
        var q: Formula = input[1];

        var assumptions1: Formula[] = copyAssumptions(this).as;
        var assumptions2: Formula[] = copyAssumptions(this).as;
        var assumptions3: Formula[] = copyAssumptions(this).as;

        assumptions2.unshift(p);
        assumptions3.unshift(q);

        var r: Formula = this.goal;

        var fmPre1: Formula = new fmDis(p, q);

        var ind1: Inductive = new Inductive(fmPre1, assumptions1);
        var ind2: Inductive = new Inductive(r, assumptions2);
        var ind3: Inductive = new Inductive(r, assumptions3);

        this.premises.push(ind1, ind2, ind3);
    }

    getInternalName(): string {
        return synDisE.getInternalName();
    }

    static getInternalName(): string {
        return "DisE";
    }

    getIsabelleProof(indent: number): string {
        var prepend = Array(indent).join("\t");
        //
        return "sorry";
    }
}

class synDisI1 extends Inductive implements InductiveInterface {

    constructor(goal: Formula, assumptions: Formula[]) {
        super(goal, assumptions);

        if (!this.isApplicable()) {
            throw new Error("Could not apply rule (synDisI1) to formula:\n" + getInternalSyntaxHTML(goal));
        }
    }

    evaluate() {
        this.inferTruthValueAux(1);
    }

    isApplicable() {
        return synDisI1.isApplicable(this.goal);
    }

    static isApplicable(goal) {
        return goal instanceof fmDis;
    }

    getPremisesAux(input: Formula[]) {
        var p: Formula = (<fmCon>this.goal).lhs;
        var inductive: Inductive = new Inductive(p, copyAssumptions(this).as);
        this.premises.push(inductive);
    }

    getInternalName(): string {
        return synDisI1.getInternalName();
    }

    static getInternalName(): string {
        return "DisI1";
    }

    getIsabelleProof(indent: number): string {
        var prepend = Array(indent).join("\t");
        //
        return "sorry";
    }
}

class synDisI2 extends Inductive implements InductiveInterface {

    constructor(goal: Formula, assumptions: Formula[]) {
        super(goal, assumptions);

        if (!this.isApplicable()) {
            throw new Error("Could not apply rule (synDisI2) to formula:\n" + getInternalSyntaxHTML(goal));
        }
    }

    evaluate() {
        this.inferTruthValueAux(1);
    }

    isApplicable() {
        return synDisI2.isApplicable(this.goal);
    }

    static isApplicable(goal) {
        return goal instanceof fmDis;
    }

    getPremisesAux(input: Formula[]) {
        var q: Formula = (<fmCon>this.goal).rhs;
        var inductive: Inductive = new Inductive(q, copyAssumptions(this).as);
        this.premises.push(inductive);
    }

    getInternalName(): string {
        return synDisI2.getInternalName();
    }

    static getInternalName(): string {
        return "DisI2";
    }

    getIsabelleProof(indent: number): string {
        var prepend = Array(indent).join("\t");
        //
        return "sorry";
    }
}

class synConE1 extends Inductive implements InductiveInterface {

    constructor(goal: Formula, assumptions: Formula[]) {
        super(goal, assumptions);

        if (!this.isApplicable()) {
            throw new Error("Could not apply rule (synConE1) to formula:\n" + getInternalSyntaxHTML(goal));
        }
    }

    evaluate() {
        this.inferTruthValueAux(1);
    }

    isApplicable() {
        return true;
    }

    static isApplicable(goal) {
        return true;
    }

    getPremisesAux(input: Formula[]) {
        if (input.length < 1) {
            throw new Error("Expecting formula q");
        }

        var q: Formula = input[0];
        var ind: Inductive = new Inductive(new fmCon(this.goal, q), copyAssumptions(this).as);
        this.premises.push(ind);
    }

    getInternalName(): string {
        return synConE1.getInternalName();
    }

    static getInternalName(): string {
        return "ConE1";
    }

    getIsabelleProof(indent: number): string {
        var prepend = Array(indent).join("\t");
        //
        return "sorry";
    }
}

class synConE2 extends Inductive implements InductiveInterface {

    constructor(goal: Formula, assumptions: Formula[]) {
        super(goal, assumptions);

        if (!this.isApplicable()) {
            throw new Error("Could not apply rule (synConE2) to formula:\n" + getInternalSyntaxHTML(goal));
        }
    }

    evaluate() {
        this.inferTruthValueAux(1);
    }

    isApplicable() {
        return true;
    }

    static isApplicable(goal) {
        return true;
    }

    getPremisesAux(input: Formula[]) {
        if (input.length < 1) {
            throw new Error("Expecting formula q");
        }

        var p: Formula = input[0];
        var ind: Inductive = new Inductive(new fmCon(p, this.goal), copyAssumptions(this).as);
        this.premises.push(ind);
    }

    getInternalName(): string {
        return synConE2.getInternalName();
    }

    static getInternalName(): string {
        return "ConE2";
    }

    getIsabelleProof(indent: number): string {
        var prepend = Array(indent).join("\t");
        //
        return "sorry";
    }
}

class synConI extends Inductive implements InductiveInterface {

    constructor(goal: Formula, assumptions: Formula[]) {
        super(goal, assumptions);

        if (!this.isApplicable()) {
            throw new Error("Could not apply rule (synConI) to formula:\n" + getInternalSyntaxHTML(goal));
        }
    }

    evaluate() {
        this.inferTruthValueAux(2);
    }

    isApplicable() {
        return synConI.isApplicable(this.goal);
    }

    static isApplicable(goal) {
        return goal instanceof fmCon;
    }

    getPremisesAux(input: Formula[]) {
        var p: Formula = (<fmCon>this.goal).lhs;
        var q: Formula = (<fmCon>this.goal).rhs;

        this.premises.push(new Inductive(p, copyAssumptions(this).as));
        this.premises.push(new Inductive(q, copyAssumptions(this).as));
    }

    getInternalName(): string {
        return synConI.getInternalName();
    }

    static getInternalName(): string {
        return "ConI";
    }

    getIsabelleProof(indent: number): string {
        var prepend = Array(indent).join("\t");
        //
        return "sorry";
    }
}

class synExiE extends Inductive implements InductiveInterface {
    c: Term;
    cIsNew: boolean;
    waitingForPCompletion: boolean;

    constructor(goal: Formula, assumptions: Formula[]) {
        super(goal, assumptions);

        if (!this.isApplicable()) {
            throw new Error("Could not apply rule (synExiE) to formula:\n" + getInternalSyntaxHTML(goal));
        }
    }

    evaluate() {
        this.inferTruthValueAux(2);

        if (!this.cIsNew)
            this.trueByAssumption = false;
    }

    isApplicable() {
        return true;
    }

    static isApplicable(goal) {
        return true;
    }

    getPremisesAux(input: any[]) {
        if (input.length < 2) {
            throw new Error("Expecting formula p and term id c");
        }

        var p: Formula = input[0];
        var c: string = input[1];

        if (p === null) {
            this.waitingForPCompletion = true;
        }

        else {
            this.getNewsAndSub(c);
        }

        var ind1 = new Inductive(new fmExi(p), copyAssumptions(this).as);

        this.premises.push(ind1);
    }

    getNewsAndSub(cString: string) {
        if (this.premises[0] === undefined || !(this.premises[0].goal instanceof fmExi))
            throw new Error("Could not find formula p");

        var p: Formula = (<fmExi>this.premises[0].goal).fm;

        var newsFmList: Formula[] = copyAssumptions(this).as;
        newsFmList.push(copyFormula(p), copyFormula(this.goal));

        this.cIsNew = news(cString, newsFmList);
        this.c = new tmFun(cString, []);

        var ind2Assumptions: Formula[] = copyAssumptions(this).as;
        ind2Assumptions.unshift(sub(0, this.c, copyFormula(p)));

        var ind2 = new Inductive(this.goal, ind2Assumptions);
        this.premises.push(ind2);
    }

    getInternalName(): string {
        return synExiE.getInternalName();
    }

    static getInternalName(): string {
        return "ExiE";
    }

    getIsabelleProof(indent: number): string {
        var prepend = Array(indent).join("\t");
        //
        return "sorry";
    }
}

class synExiI extends Inductive implements InductiveInterface {

    constructor(goal: Formula, assumptions: Formula[]) {
        super(goal, assumptions);

        if (!this.isApplicable()) {
            throw new Error("Could not apply rule (synExiI) to formula:\n" + getInternalSyntaxHTML(goal));
        }
    }

    evaluate() {
        this.inferTruthValueAux(1);
    }

    isApplicable() {
        return synExiI.isApplicable(this.goal);
    }

    static isApplicable(goal) {
        return goal instanceof fmExi;
    }

    getPremisesAux(input: any[]) {
        if (input.length < 1) {
            throw new Error("Expecting term t");
        }

        var t: Term = input[0];

        var p: Formula = (<fmExi>this.goal).fm;
        var indFm: Formula = sub(0, t, copyFormula(p));

        this.premises.push(new Inductive(indFm, copyAssumptions(this).as));
    }

    getInternalName(): string {
        return synExiI.getInternalName();
    }

    static getInternalName(): string {
        return "ExiI";
    }

    getIsabelleProof(indent: number): string {
        var prepend = Array(indent).join("\t");
        //
        return "sorry";
    }
}

class synUniE extends Inductive implements InductiveInterface {
    waitingForTermSelection: boolean = true;

    constructor(goal: Formula, assumptions: Formula[]) {
        super(goal, assumptions);

        if (!this.isApplicable()) {
            throw new Error("Could not apply rule (synUniE) to formula:\n" + getInternalSyntaxHTML(goal));
        }
    }

    evaluate() {
        this.inferTruthValueAux(1);
    }

    isApplicable() {
        return synUniE.isApplicable(this.goal);
    }

    static isApplicable(goal) {
        return getFreeTerms(goal).length > 0;
    }

    static subReverse(replacement: number, searchFor: { term: Term, occs: number[] }, replaceIn: Formula, occurenceCount): { f: Formula, n: number } {

        if (replaceIn instanceof fmPre) {
            var termList: Term[] = [];

            var n = occurenceCount;

            replaceIn.tms.forEach(t => {
                var result = this.subReverseT(replacement, searchFor, t, n);

                termList.push(result.t);

                n = result.n;
            });

            return {
                f: new fmPre(replaceIn.id, termList),
                n: n
            };
        }

        else if (replaceIn instanceof fmExi) {
            var result = this.subReverse(replacement + 1, {
                term: inct(searchFor.term),
                occs: searchFor.occs
            }, replaceIn.fm, occurenceCount);

            return {
                f: new fmExi(result.f),
                n: result.n
            };
        }

        else if (replaceIn instanceof fmUni) {
            var result = this.subReverse(replacement + 1, {
                term: inct(searchFor.term),
                occs: searchFor.occs
            }, replaceIn.fm, occurenceCount);

            return {
                f: new fmUni(result.f),
                n: result.n
            };
        }

        else if (replaceIn instanceof fmFalsity) {
            return {
                f: new fmFalsity(),
                n: occurenceCount
            };
        }

        else if (replaceIn instanceof FormulaTwoArg) {
            var lhsResult = this.subReverse(replacement, searchFor, replaceIn.lhs, occurenceCount);
            var rhsResult = this.subReverse(replacement, searchFor, replaceIn.rhs, lhsResult.n);

            if (replaceIn instanceof fmCon) {
                return {
                    f: new fmCon(lhsResult.f, rhsResult.f),
                    n: rhsResult.n
                };
            }

            else if (replaceIn instanceof fmDis) {
                return {
                    f: new fmDis(lhsResult.f, rhsResult.f),
                    n: rhsResult.n
                };
            }

            else if (replaceIn instanceof fmImp) {
                return {
                    f: new fmImp(lhsResult.f, rhsResult.f),
                    n: rhsResult.n
                };
            }
        }
    }

    static subReverseT(replacement: number, searchFor: { term: Term, occs: number[] }, replaceIn: Term, occurenceCount): { t: Term, n: number } {

        if (replaceIn instanceof tmFun) {
            var found: boolean = equalFormulas(replaceIn, searchFor.term);

            if (found) {

                return {
                    t: searchFor.occs.some(m => m == occurenceCount) ? new tmVar(replacement) : replaceIn,
                    n: occurenceCount + 1
                };

            } else {

                var termList: Term[] = [];

                var n = occurenceCount;

                replaceIn.tms.forEach(t => {
                    var result = this.subReverseT(replacement, searchFor, t, n);

                    termList.push(result.t);

                    n = result.n;
                });

                return {
                    t: new tmFun(replaceIn.id, termList),
                    n: n
                };
            }
        }

        else if (replaceIn instanceof tmVar) {
            var found: boolean = equalFormulas(replaceIn, searchFor.term);

            var newTerm = found && searchFor.occs.some(m => m == occurenceCount) ? new tmVar(replacement) : new tmVar(replacement > replaceIn.nat ? replaceIn.nat : replaceIn.nat + 1);

            var newOccurenceCount = found ? occurenceCount + 1 : occurenceCount;

            return {
                t: newTerm,
                n: newOccurenceCount
            };
        }
    }

    getPremisesAux(input: { term: Term, occs: number[] }[]) {
        if (input.length !== 1) {
            console.log(input);
            throw new Error("Expecting one term to replace");
        }

        var termOcc = input[0];

        var fm: Formula = new fmUni(synUniE.subReverse(0, termOcc, this.goal, 0).f);

        // Create and push premise
        this.premises.push(new Inductive(fm, copyAssumptions(this).as));
    }

    getInternalName(): string {
        return synUniE.getInternalName();
    }

    static getInternalName(): string {
        return "UniE";
    }

    getIsabelleProof(indent: number): string {
        var prepend = Array(indent).join("\t");
        //
        return "sorry";
    }

    waiting(): number {
        return this.premises.reduce((acc, p) => acc + p.waiting(), 0) + (this.waitingForTermSelection ? 1 : 0);
    }
}

class synUniI extends Inductive implements InductiveInterface {
    c: Term;
    cIsNew: boolean;

    constructor(goal: Formula, assumptions: Formula[]) {
        super(goal, assumptions);

        if (!this.isApplicable()) {
            throw new Error("Could not apply rule (synUniI) to formula:\n" + getInternalSyntaxHTML(goal));
        }
    }

    evaluate() {
        this.inferTruthValueAux(1);

        this.trueByAssumption = this.trueByAssumption && this.cIsNew;
    }

    isApplicable() {
        return synUniI.isApplicable(this.goal);
    }

    static isApplicable(goal) {
        return goal instanceof fmUni;
    }

    getPremisesAux(input: string[]) {
        if (input.length < 1) {
            throw new Error("Expecting term id c");
        }

        var c: string = input[0];
        this.c = new tmFun(c, []);

        var p: Formula = (<fmUni>this.goal).fm;

        var newsFmList: Formula[] = copyAssumptions(this).as;
        newsFmList.push(copyFormula(p), copyFormula(this.goal));

        this.cIsNew = news(c, newsFmList);

        var l = copyFormula(p);

        var subResult = sub(0, this.c, l);

        this.premises.push(
            new Inductive(subResult, copyAssumptions(this).as));
    }

    getInternalName(): string {
        return synUniI.getInternalName();
    }

    static getInternalName(): string {
        return "UniI";
    }

    getIsabelleProof(indent: number): string {
        var prepend = Array(indent).join("\t");
        //
        return "sorry";
    }
}

/*
 * sub, subs, subl, subt
 */

function sub(n: number, s: Term, fm: Formula): Formula {
    var fmReturn: Formula;

    if (fm instanceof fmFalsity) {
        return new fmFalsity();
    }

    else if (fm instanceof fmPre) {
        var i = (<fmPre>fm).id;
        var tms = subl(n, s, (<fmPre>fm).tms);
        return new fmPre(i, tms);
    }

    else if (fm instanceof fmImp) {
        var lhs = sub(n, s, (<fmImp>fm).lhs);
        var rhs = sub(n, s, (<fmImp>fm).rhs);
        return new fmImp(lhs, rhs);
    }

    else if (fm instanceof fmDis) {
        var lhs = sub(n, s, (<fmDis>fm).lhs);
        var rhs = sub(n, s, (<fmDis>fm).rhs);
        return new fmDis(lhs, rhs);
    }

    else if (fm instanceof fmCon) {
        var lhs = sub(n, s, (<fmCon>fm).lhs);
        var rhs = sub(n, s, (<fmCon>fm).rhs);
        return new fmCon(lhs, rhs);
    }

    else if (fm instanceof fmExi) {
        return new fmExi(sub(n + 1, inct(s), (<fmExi>fm).fm));
    }

    else if (fm instanceof fmUni) {
        return new fmUni(sub(n + 1, inct(s), (<fmUni>fm).fm));
    }

    else {
        throw new Error("Unrecognized formula type");
    }
}

function subl(n: number, s: Term, ts: Term[]): Term[] {
    if (ts.length == 0)
        return [];
    else {
        var t = ts[0];

        return [subt(n, s, t)].concat(subl(n, s, ts.slice(1)));

    }
}

function subt(n: number, s: Term, t: Term): Term {

    if (t instanceof tmVar) {
        var tv = <tmVar>t;

        if (tv.nat == n)
            return s;
        else if (tv.nat > n)
            return new tmVar(tv.nat - 1);
        else
            return new tmVar(tv.nat);
    }

    else if (t instanceof tmFun) {
        return new tmFun((<tmFun>t).id, subl(n, s, (<tmFun>t).tms));
    }

    else {
        throw new Error("Unrecognized term type");
    }
}

/*
 * newt, newl, new (named new1 due to reserved keyword), news
 */

function news(c: string, fmList: Formula[]): boolean {
    if (fmList.length == 0)
        return true;
    else {
        var p = fmList[0]

        if (new1(c, p))
            return news(c, fmList.slice(1));
        else
            return false;
    }
}

function new1(c: string, fm: Formula): boolean {
    if (fm instanceof fmFalsity)
        return true;

    else if (fm instanceof fmPre) {
        var l = (<fmPre>fm).tms;
        return newl(c, l);
    }

    else if (fm instanceof fmImp) {
        var p = (<fmImp>fm).lhs;
        var q = (<fmImp>fm).rhs;

        if (new1(c, p))
            return new1(c, q);
        else
            return false;
    }

    else if (fm instanceof fmDis) {
        var p = (<fmDis>fm).lhs;
        var q = (<fmDis>fm).rhs;

        if (new1(c, p))
            return new1(c, q);
        else
            return false;

    }

    else if (fm instanceof fmCon) {
        var p = (<fmCon>fm).lhs;
        var q = (<fmCon>fm).rhs;

        if (new1(c, p))
            return new1(c, q);
        else
            return false;

    }

    else if (fm instanceof fmExi)
        return new1(c, (<fmExi>fm).fm);

    else if (fm instanceof fmUni)
        return new1(c, (<fmUni>fm).fm);

    else
        throw new Error("Unrecognized formula type");
}

function newl(c: string, ts: Term[]): boolean {
    if (ts.length == 0)
        return true;
    else {
        var t = ts[0];

        if (newt(c, t))
            return newl(c, ts.slice(1));
        else
            return false;
    }
}

function newt(c: string, t: Term): boolean {
    if (t instanceof tmVar)
        return true;

    else if (t instanceof tmFun) {
        var i = (<tmFun>t).id;
        var l = (<tmFun>t).tms;

        if (i === c)
            return false;
        else
            return newl(c, l);
    }

    else
        throw new Error("Unrecognized term type");
}


/*
 * incl, inct
 */

function inct(t: Term): Term {
    if (t instanceof tmVar)
        return new tmVar((<tmVar>t).nat + 1);
    else if (t instanceof tmFun)
        return new tmFun((<tmFun>t).id, incl((<tmFun>t).tms));
    else if (t === null)
        return null;
}

function incl(ts: Term[]): Term[] {
    if (ts === null)
        return null;
    if (ts.length == 0)
        return [];
    else {
        var t = ts[0];

        return [inct(t)].concat(incl(ts.slice(1)));
    }
}


function dect(t: Term): Term {
    if (t instanceof tmVar)
        return new tmVar((<tmVar>t).nat - 1);
    else if (t instanceof tmFun)
        return new tmFun((<tmFun>t).id, decl((<tmFun>t).tms));
    else if (t === null)
        return null;
}

function decl(ts: Term[]): Term[] {
    if (ts === null)
        return null;
    if (ts.length == 0)
        return [];
    else {
        var t = ts[0];

        return [dect(t)].concat(decl(ts.slice(1)));
    }
}

//
// Determines validity of proof
//
function isValidProof(x: Inductive): boolean {
    try {
        return validateProof(x) && x.premises.every(v => isValidProof(v));
    } catch (e) {
        console.log(e);
        console.log(x);
        return false;
    }
}

function validateProof(x): boolean {
    function subCheck(fm1: Formula, fm2: Formula): { x: boolean, y: { t: Term, n: number }[] } {
        var terms = subCheckF(fm1, fm2, 0);

        var r: boolean = true;

        if (terms.length === 0)
            r = false;

        else if (!terms.every((v, i) => terms.slice(i).every(w => equalFormulas(v.t, w.t))))
            r = false;

        return { x: r, y: terms };
    };

    function subCheckT(tm1: Term, tm2: Term, n: number): { t: Term, n: number }[] {
        if (tm1 instanceof tmVar) {
            if (tm1.nat === n)
                return [{ t: tm2, n: n }];
            else
                return [];
        }

        else if (tm1 instanceof tmFun && tm2 instanceof tmFun) {
            return [];
        }

        else {
            console.log(tm1, tm2, n);
            throw new Error("Unexpected type of inputs");
        }
    };

    function subCheckF(fm1: Formula, fm2: Formula, n: number): { t: Term, n: number }[] {
        if (fm1 instanceof fmPre && fm2 instanceof fmPre) {
            if (fm1.tms === null || fm2.tms === null)
                return [];

            else {
                var r: { t: Term, n: number }[] = [];
                fm1.tms.forEach((v, i) => r = r.concat(subCheckT(v, fm2.tms[i], n)));
                return r;
            }
        }

        else if (fm1 instanceof fmUni && fm2 instanceof fmUni || fm1 instanceof fmExi && fm2 instanceof fmExi)
            return subCheckF(fm1.fm, fm2.fm, n + 1);

        else if (fm1 instanceof fmCon && fm2 instanceof fmCon || fm1 instanceof fmDis && fm2 instanceof fmDis || fm1 instanceof fmImp && fm2 instanceof fmImp)
            return subCheckF(fm1.lhs, fm2.lhs, n).concat(subCheckF(fm1.rhs, fm2.rhs, n));

        else if (fm1 instanceof fmFalsity && fm2 instanceof fmFalsity)
            return [];

        else {
            console.log(fm1, fm2, n);
            throw new Error("Unexpected type of inputs");
        }
    }

    if (x instanceof synBool) {
        if (x.premises.length != 1)
            throw new Error("Unexpected premise length");

        var p = x.goal;

        if (!equalFormulas(x.premises[0].goal, new fmFalsity()))
            throw new Error("Unmatching formulas");

        if (x.premises[0].assumptions.length == 0)
            throw new Error("Expected at least assumption in premise");

        if (!equalFormulas(x.premises[0].assumptions[0], new fmImp(p, new fmFalsity)))
            throw new Error("Unmatching formulas");

        if (!equalFormulas(x.premises[0].assumptions.slice(1), x.assumptions))
            throw new Error("Unmatching formulas");

    } else if (x instanceof synImpE) {
        if ((<synImpE>x).premises.length != 2)
            throw new Error("Unexpected premise length");

        var q = (<synImpE>x).goal;
        var p = (<synImpE>x).premises[1].goal;

        if (!(equalFormulas((<synImpE>x).assumptions, (<synImpE>x).premises[0].assumptions) && equalFormulas((<synImpE>x).assumptions, (<synImpE>x).premises[1].assumptions)))
            throw new Error("Unmatching formulas");

        if (!equalFormulas((<synImpE>x).premises[0].goal, new fmImp(p, q)))
            throw new Error("Unmatching formulas");

    } else if (x instanceof synImpI) {
        if ((<synImpI>x).premises.length != 1)
            throw new Error("Unexpected premise length");

        if ((<synImpI>x).premises[0].assumptions.length == 0)
            throw new Error("Expected at least assumption in premise");

        var q = (<synImpI>x).premises[0].goal;
        var p = (<synImpI>x).premises[0].assumptions[0];

        if (!equalFormulas((<synImpI>x).goal, new fmImp(p, q)))
            throw new Error("Unmatching formulas");

        if (!equalFormulas((<synImpI>x).assumptions, (<synImpI>x).premises[0].assumptions.slice(1)))
            throw new Error("Unmatching formulas");

    } else if (x instanceof synDisE) {
        if ((<synDisE>x).premises.length != 3)
            throw new Error("Unexpected premise length");

        var r = (<synDisE>x).goal;
        var p = (<synDisE>x).premises[1].assumptions[0];
        var q = (<synDisE>x).premises[2].assumptions[0];

        if (!equalFormulas((<synDisE>x).premises[0].goal, new fmDis(p, q)))
            throw new Error("Unmatching formulas");

        if (!equalFormulas((<synDisE>x).premises[1].goal, r))
            throw new Error("Unmatching formulas");

        if (!equalFormulas((<synDisE>x).premises[2].goal, r))
            throw new Error("Unmatching formulas");

        if (!equalFormulas((<synDisE>x).assumptions, (<synDisE>x).premises[1].assumptions.slice(1)))
            throw new Error("Unmatching formulas");

        if (!equalFormulas((<synDisE>x).assumptions, (<synDisE>x).premises[2].assumptions.slice(1)))
            throw new Error("Unmatching formulas");

    } else if (x instanceof synDisI1) {
        if ((<synDisI1>x).premises.length != 1)
            throw new Error("Unexpected premise length");

        if (!((<synDisI1>x).goal instanceof fmDis))
            throw new Error("Unexpected type of conclusion goal");

        var p = (<fmDis>(<synDisI1>x).goal).lhs
        var q = (<fmDis>(<synDisI1>x).goal).rhs

        if (!equalFormulas(p, (<synDisI1>x).premises[0].goal))
            throw new Error("Unmatching formulas");

        if (!equalFormulas((<synDisI1>x).assumptions, (<synDisI1>x).premises[0].assumptions))
            throw new Error("Unmatching formulas");

    } else if (x instanceof synDisI2) {
        if ((<synDisI2>x).premises.length != 1)
            throw new Error("Unexpected premise length");

        if (!((<synDisI2>x).goal instanceof fmDis))
            throw new Error("Unexpected type of conclusion goal");

        var p = (<fmDis>(<synDisI2>x).goal).lhs
        var q = (<fmDis>(<synDisI2>x).goal).rhs

        if (!equalFormulas(q, (<synDisI2>x).premises[0].goal))
            throw new Error("Unmatching formulas");

        if (!equalFormulas((<synDisI2>x).assumptions, (<synDisI2>x).premises[0].assumptions))
            throw new Error("Unmatching formulas");

    } else if (x instanceof synConE1) {
        if ((<synConE1>x).premises.length != 1)
            throw new Error("Unexpected premise length");

        if (!((<synConE1>x).premises[0].goal instanceof fmCon))
            throw new Error("Unexpected type of premise goal");

        var p = (<fmCon>(<synConE1>x).premises[0].goal).lhs
        var q = (<fmCon>(<synConE1>x).premises[0].goal).rhs

        if (!equalFormulas(p, (<synConE1>x).goal))
            throw new Error("Unmatching formulas");

        if (!equalFormulas((<synConE1>x).assumptions, (<synConE1>x).premises[0].assumptions))
            throw new Error("Unmatching formulas");

    } else if (x instanceof synConE2) {
        if ((<synConE2>x).premises.length != 1)
            throw new Error("Unexpected premise length");

        if (!((<synConE2>x).premises[0].goal instanceof fmCon))
            throw new Error("Unexpected type of premise goal");

        var p = (<fmCon>(<synConE2>x).premises[0].goal).lhs
        var q = (<fmCon>(<synConE2>x).premises[0].goal).rhs

        if (!equalFormulas(q, (<synConE2>x).goal))
            throw new Error("Unmatching formulas");

        if (!equalFormulas((<synConE2>x).assumptions, (<synConE2>x).premises[0].assumptions))
            throw new Error("Unmatching formulas");

    } else if (x instanceof synConI) {
        if ((<synConI>x).premises.length != 2)
            throw new Error("Unexpected premise length");

        var p = (<synConI>x).premises[0].goal;
        var q = (<synConI>x).premises[1].goal;

        if (!equalFormulas((<synConI>x).goal, new fmCon(p, q)))
            throw new Error("Unmatching formulas");

        if (!equalFormulas((<synConI>x).assumptions, (<synConI>x).premises[0].assumptions))
            throw new Error("Unmatching formulas");

        if (!equalFormulas((<synConI>x).assumptions, (<synConI>x).premises[1].assumptions))
            throw new Error("Unmatching formulas");


    } else if (x instanceof synExiE) {
        if (!((<synExiE>x).premises[0].goal instanceof fmExi))
            throw new Error("Unexpected type of premise goal");

        var p = (<fmExi>(<synExiE>x).premises[0].goal).fm;

        if ((<synExiE>x).waitingForPCompletion) {
            if ((<synExiE>x).premises.length != 1)
                throw new Error("Unexpected premise length");
        } else {
            if ((<synExiE>x).premises.length != 2)
                throw new Error("Unexpected premise length");

            if ((<synExiE>x).premises[1].assumptions.length == 0)
                throw new Error("Expected at least one assumption in premise");

            var q = (<synExiE>x).goal

            if (!equalFormulas(q, (<synExiE>x).premises[1].goal))
                throw new Error("Unmatching formulas");

            if (!equalFormulas((<synExiE>x).assumptions, (<synExiE>x).premises[0].assumptions))
                throw new Error("Unmatching formulas");

            if (!equalFormulas((<synExiE>x).assumptions, (<synExiE>x).premises[1].assumptions.slice(1)))
                throw new Error("Unmatching formulas");

            if (!equalFormulas(sub(0, (<synExiE>x).c, p), (<synExiE>x).premises[1].assumptions[0]))
                throw new Error("Invalid substitution");

            if (!((<synExiE>x).cIsNew && news((<tmFun>(<synExiE>x).c).id, [p, q].concat((<synExiE>x).assumptions))))
                throw new Error("Term is not new.");
        }

    } else if (x instanceof synExiI) {
        if ((<synExiI>x).premises.length != 1)
            throw new Error("Unexpected premise length");

        if (!((<synExiI>x).goal instanceof fmExi))
            throw new Error("Unexpected type of conclusion goal");

        var p = (<fmExi>(<synExiI>x).goal).fm;

        if (!equalFormulas((<synExiI>x).assumptions, (<synExiI>x).premises[0].assumptions))
            throw new Error("Unmatching formulas");

        var sc = subCheck(p, (<synExiI>x).premises[0].goal);

        if (!sc.x) {
            throw new Error("Invalid substitution");
        }

    } else if (x instanceof synUniE) {
        if ((<synUniE>x).waitingForTermSelection) {
            if ((<synUniE>x).premises.length != 0)
                throw new Error("Unexpected premise length");
        } else {
            if ((<synUniE>x).premises.length != 1)
                throw new Error("Unexpected premise length");

            var p = (<fmUni>(<synUniE>x).premises[0].goal).fm;

            if (!equalFormulas((<synUniE>x).assumptions, (<synUniE>x).premises[0].assumptions))
                throw new Error("Unmatching formulas");

            if (!subCheck(p, (<synUniE>x).goal).x)
                throw new Error("Invalid substitution");
        }

    } else if (x instanceof synUniI) {
        if ((<synUniI>x).premises.length != 1)
            throw new Error("Unexpected premise length");

        if (!((<synUniI>x).goal instanceof fmUni))
            throw new Error("Unexpected type of conclusion goal");

        var p = (<fmUni>(<synUniI>x).goal).fm;

        if (!equalFormulas((<synUniI>x).assumptions, (<synUniI>x).premises[0].assumptions))
            throw new Error("Unmatching formulas");

        if (!equalFormulas((<synUniI>x).premises[0].goal, sub(0, (<synUniI>x).c, p)))
            throw new Error("Invalid substitution");

        if (!((<synUniI>x).cIsNew && news((<tmFun>(<synUniI>x).c).id, [p].concat((<synUniI>x).assumptions))))
            throw new Error("Term is not new");

    } else if (x instanceof Inductive) {
        if ((<Inductive>x).trueByAssumption) {
            if ((<Inductive>x).assumptions.every(v => !equalFormulas(v, (<Inductive>x).goal))) {
                throw new Error("Not a valid assumption");
            }
        }
    }

    else {
        console.log(x);
        throw new Error("Unexpected type of x");
    }

    return true;
}

//
// Return a string representation of the proof
//
function encodeProof(x: any): string {
    if (x === null || x === undefined)
        return ".";

    var s: string = "";

    if (x instanceof Inductive) {
        var ind: Inductive = x;

        s += x.getInternalName();

        s += "{" + encodeProof(ind.goal) + "}";

        s += "[";

        ind.assumptions.forEach((v, i) => {
            s += (i > 0 ? "," : "") + encodeProof(v);
        });

        s += "]";

        //
        // Handle inductive types with additional arguments
        //
        if (ind instanceof synExiE) {
            s += "{" + encodeProof((<synExiE>ind).c) + "," + ((<synExiE>ind).cIsNew ? "1" : "0") + "," + ((<synExiE>ind).waitingForPCompletion ? "1" : "0") + "}";
        }

        else if (ind instanceof synUniE) {
            s += "{" + ((<synUniE>ind).waitingForTermSelection ? "1" : "0") + "}";
        }

        else if (ind instanceof synUniI) {
            s += "{" + encodeProof((<synUniI>ind).c) + "," + ((<synUniI>ind).cIsNew ? "1" : "0") + "}";
        }

        if (ind.premises.length > 0) {

            s += ":";

            ind.premises.forEach(v => {
                s += "{" + encodeProof(v) + "}";
            });

        }
    }

    else if (x instanceof FormulaOneArg) {
        var foa: FormulaOneArg = <FormulaOneArg>x;

        s += foa.getInternalName();

        s += "{" + encodeProof(foa.fm) + "}";
    }

    else if (x instanceof FormulaTwoArg) {
        var fta: FormulaTwoArg = <FormulaTwoArg>x;

        s += fta.getInternalName();

        s += "{" + encodeProof(fta.lhs) + "}";
        s += "{" + encodeProof(fta.rhs) + "}";
    }

    else if (x instanceof fmPre) {
        var fmp: fmPre = <fmPre>x;

        s += fmp.getInternalName();

        s += "{";
        s += (fmp.id === null ? "." : fmp.id);
        s += "}";

        s += "{";

        if (fmp.tms === null)
            s += ".";
        else if (fmp.tms.length > 0) {
            s += "[";
            fmp.tms.forEach(v => {
                s += encodeProof(v) + ",";
            });

            // Remove last comma
            s = s.substr(0, s.length - 1);


            s += "]";
        }

        s += "}";
    }

    else if (x instanceof fmFalsity) {
        s += (<fmFalsity>x).getInternalName();
    }

    else if (x instanceof tmVar) {
        var tmv: tmVar = <tmVar>x;

        s += tmv.getInternalName() + "{" + tmv.nat.toString() + "}";
    }

    else if (x instanceof tmFun) {
        var tmf: tmFun = <tmFun>x;

        s += tmf.getInternalName();

        s += "{";
        s += (tmf.id === null ? "." : tmf.id);
        s += "}";
        s += "{";

        if (tmf.tms === null)
            s += ".";
        else if (tmf.tms.length > 0) {
            s += "[";
            tmf.tms.forEach(v => {
                s += encodeProof(v) + ",";
            });

            // Remove last comma
            s = s.substr(0, s.length - 1);

            s += "]";
        }

        s += "}";
    }

    else {
        console.log(x);
        throw new Error("Unexpected type of x");
    }

    return s;
}

//
// Build proof structure from string representation built by encoder
//
function decodeProof(x: string): Inductive[] {
    // Remove comment lines and then white spaces
    var y = x.replace(/^(\.|\#)[^\r\n]*/gm, "").split(/\s/);

    y = y.filter(s => { return s !== "" });

    var z: Inductive[] = [];

    var ok = true;

    y.forEach(p => {
        var dp = decodeProofAux(p);

        if (dp === null || dp === undefined)
            ok = false;

        else if (!isValidProof(dp))
            ok = false

        else
            z.push(dp);
    });

    if (!ok)
        return null;

    return z;
}

// Array of inductive classes
var inductiveClasses = [Inductive, synBool, synConE1, synConE2, synConI, synDisE, synDisI1, synDisI2, synExiE, synExiI, synImpE, synImpI, synUniE, synUniI];

// Array of formula classes
var formulaClasses = [fmCon, fmDis, fmExi, fmFalsity, fmImp, fmPre, fmUni];

// Array of term classes
var termClasses = [tmFun, tmVar];

//
// Build inductive regex
//
var indNameMatch = "";

inductiveClasses.forEach(v => {
    indNameMatch += v.getInternalName() + "|";
});

indNameMatch = indNameMatch.substr(0, indNameMatch.length - 1);

var indReg = new RegExp("^(" + indNameMatch + ")");

//
// Build formula regex
//

var fmNameMatch = "";

formulaClasses.forEach(v => {
    fmNameMatch += v.getInternalName() + "|";
});

fmNameMatch = fmNameMatch.substr(0, fmNameMatch.length - 1);

var fmReg = new RegExp("^(" + fmNameMatch + ")");

//
// Build term regex
//

var tmNameMatch = "";

termClasses.forEach(v => {
    tmNameMatch += v.getInternalName() + "|";
});

tmNameMatch = tmNameMatch.substr(0, tmNameMatch.length - 1);

var tmReg = new RegExp("^(" + tmNameMatch + ")");

//
// Decode proof (aux)
//

function decodeProofAux(x: string): any {
    //
    // Special unknown symbol
    //

    if (x === ".")
        return null;

    var m: string[];

    //
    // Match against inductive types
    //
    m = x.match(indReg);

    if (m !== null) {
        var ind: Inductive;

        var ex = extractArgs(x, true);

        // Extract arguments
        var indName: string = m[1];
        var indGoal: string = ex.args.shift();
        var indAssumptions: string = ex.assum;
        var indAdditionalArgs: string[] = (ex.args[0] !== undefined && ex.args[0].match(indReg) === null ? ex.args.shift() : "").split(",");
        var indPremises: string = (ex.args.length > 0) ? "" : undefined;

        while (ex.args.length > 0)
            indPremises += "{" + ex.args.shift() + "}";

        // Parse goal
        var goal: Formula = decodeProofAux(indGoal);

        // Make sure that goal was parsed correctly
        if (goal === undefined)
            return;

        // Parse assumptions
        var assumptions: Formula[] = [];

        if (indAssumptions !== undefined)
            ((e: string) => {
                var es: string[] = [];
                var b = 0, c = 0;

                for (var i = 0; i < e.length; i++) {
                    if (e[i] === "{")
                        b++;
                    else if (e[i] === "}")
                        b--;

                    if (e[i] === "," && b === 0) {
                        c++;
                    } else {
                        if (es[c] === undefined)
                            es[c] = "";
                        es[c] += e[i];
                    }
                }

                return es;
            }).call(null, indAssumptions).forEach(v => {
                var a: Formula = decodeProofAux(v);

                // Make sure that formula was parsed correctly
                if (a === undefined)
                    return;

                assumptions.push(a);
            });

        // Parse premises
        var premises: Inductive[] = [];

        if (indPremises !== undefined) {
            var premisesStrs = extractArgs(indPremises);

            premisesStrs.forEach(v => {
                var prem: Inductive = decodeProofAux(v);

                if (prem === undefined)
                    return;

                premises.push(prem);
            });
        }

        // Instantiate inductive object
        inductiveClasses.some(v => {
            if (indName === v.getInternalName()) {
                eval("ind = new v.prototype.constructor(goal, assumptions);");
                return true;
            }
        });

        ind.goal = goal;
        ind.assumptions = assumptions;
        ind.premises = premises;
        ind.checkGoal();

        //
        // Handle inductive types with additional arguments
        //
        if (ind instanceof synExiE && indAdditionalArgs.length >= 3) {
            var c = decodeProofAux(indAdditionalArgs[0]);
            var cIsNew = indAdditionalArgs[1] === "1";
            var waitingForPCompletion = indAdditionalArgs[2] === "1";

            if (c === undefined)
                return;

            (<synExiE>ind).c = c;
            (<synExiE>ind).cIsNew = cIsNew;
            (<synExiE>ind).waitingForPCompletion = waitingForPCompletion;
        }

        else if (ind instanceof synUniE && indAdditionalArgs.length >= 1) {
            var waitingForTermSelection = indAdditionalArgs[0] === "1";

            (<synUniE>ind).waitingForTermSelection = waitingForTermSelection;
        }

        else if (ind instanceof synUniI && indAdditionalArgs.length >= 2) {
            var c = decodeProofAux(indAdditionalArgs[0]);
            var cIsNew = indAdditionalArgs[1] === "1";

            if (c === undefined)
                return;

            (<synUniI>ind).c = c;
            (<synUniI>ind).cIsNew = cIsNew;
        }

        return ind;
    }

    //
    // Match against formula types
    //
    m = x.match(fmReg);

    if (m !== null) {
        // Construct new object generically
        var fm: Formula;

        var fmName = m[1];

        formulaClasses.some(v => {
            if (fmName === (<typeof Formula>v).getInternalName()) {
                eval("fm = new v.prototype.constructor(null, null);");
                return true;
            }
        });

        // Make sure that formula was parsed correctly
        if (fm === undefined)
            return;

        // Extract arguments
        var args: string[] = extractArgs(x);

        //
        // Choose instantiation procedure based on formula type
        //

        if (fm instanceof FormulaOneArg) {
            var fmInner: Formula = decodeProofAux(args[0]);

            // Make sure that formula was parsed correctly
            if (fmInner === undefined)
                return;

            (<FormulaOneArg>fm).fm = fmInner;
        }

        else if (fm instanceof FormulaTwoArg) {
            var fmInnerLHS: Formula = decodeProofAux(args[0]);
            var fmInnerRHS: Formula = decodeProofAux(args[1]);

            // Make sure that formulas were parsed correctly
            if (fmInnerLHS === undefined || fmInnerRHS === undefined)
                return;

            (<FormulaTwoArg>fm).lhs = fmInnerLHS;
            (<FormulaTwoArg>fm).rhs = fmInnerRHS;

        }

        else if (fm instanceof fmPre) {
            if (args[0] !== ".")
                (<fmPre>fm).id = args[0];

            if (args[1] !== ".") {
                (<fmPre>fm).tms = [];

                if (args[1] !== undefined) {
                    var tmListStr = args[1].match(/(\[(.*)\])|(.*)/)

                    if (tmListStr === null)
                        return;

                    outerMostSplit(tmListStr[2] === undefined ? tmListStr[3] : tmListStr[2], ",").forEach(v => {
                        var tm: Term = decodeProofAux(v);

                        // Make sure that term was parsed correctly
                        if (tm === undefined)
                            return;

                        (<fmPre>fm).tms.push(tm);
                    });
                }
            }
        }

        else if (fm instanceof fmFalsity) {
            // Do nothing
        }

        else {
            console.log(fm);
            throw new Error("Unexpected type of fm");
        }

        return fm;
    }

    //
    // Match against formula types
    //
    m = x.match(tmReg);

    if (m !== null) {
        // Construct new object generically
        var tm: Term;

        var tmName = m[1];

        termClasses.some(v => {
            if (tmName === v.getInternalName()) {
                eval("tm = new v.prototype.constructor(null, null);");
                return true;
            }
        });

        // Make sure that formula was parsed correctly
        if (tm === undefined)
            return;

        // Extract arguments
        var args: string[] = extractArgs(x);

        if (tm instanceof tmVar) {
            (<tmVar>tm).nat = +args[0];
        }

        else if (tm instanceof tmFun) {
            if (args[0] !== ".")
                (<tmFun>tm).id = args[0].replace("'", "*");

            if (args[1] !== ".") {
                (<tmFun>tm).tms = [];

                if (args[1] !== undefined) {
                    var tmListStr = args[1].match(/(\[(.*)\])|(.*)/)

                    if (tmListStr === null)
                        return;

                    outerMostSplit(tmListStr[2] === undefined ? tmListStr[3] : tmListStr[2], ",").forEach(v => {
                        var tmArg = decodeProofAux(v);

                        // Make sure that term was parsed correctly
                        if (tmArg === undefined)
                            return;

                        (<tmFun>tm).tms.push(tmArg);
                    });
                }
            }
        }

        else {
            console.log(tm);
            throw new Error("Unexpected type of tm");
        }

        return tm;
    }

    else {
        return;
    }
}

//
// Split only outside of {}'s
//

function outerMostSplit(x: string, seperator: string): string[] {
    var r: string[] = [];

    var nestedBrackets = 0;
    var currentArgument = 0;

    for (var i = 0; i < x.length; i++) {

        if (x[i] === "{") {
            nestedBrackets++;
        }

        else if (x[i] === "}") {
            nestedBrackets--;
        }

        else if (x[i] === seperator && nestedBrackets === 0) {
            currentArgument++;

            continue;
        }

        if (r.length == currentArgument)
            r[currentArgument] = "";

        r[currentArgument] += x[i];
    }

    return r;
}

//
// Helper function to deal with problem of well-balanced curly braces / brackets
//
function extractArgs(x: string, isInd: boolean = false): any {
    if (x === undefined || x === null)
        return null;

    var args: string[] = [""];
    var c = 0, b = 0;

    var assumStr: string = "";
    var d = 0;

    for (var i = 0; i < x.length; i++) {

        if (x[i] === "{") {
            b++;

            if (b == 1 && d == 0)
                continue;
        }

        else if (x[i] === "}") {
            b--;

            if (b == 0 && d == 0) {

                c++;

                if (i !== x.length - 1)
                    args[c] = "";

                continue;
            }
        }

        else if (x[i] === "[" && b === 0) {
            d++;

            if (d == 1)
                continue;
        }

        else if (x[i] === "]" && b === 0) {
            d--;
        }

        if (isInd && d > 0) {
            assumStr += x[i];
        }

        else if (b > 0 && d == 0) {
            args[c] += x[i];
        }
    }

    return !isInd ? args : { args: args, assum: assumStr };
}

function isValidProofCode(x: string) {
    var dp = decodeProof(x);

    return dp !== null && dp !== undefined && dp.length > 0;
}

// Deep copy of a list of assumptions
function copyAssumptions(x: Inductive, refs: any[] = null): { as: Formula[]; n: number } {
    var assumptions: Formula[] = [];

    var numRefs = 0;

    x.assumptions.forEach(function (v) {
        if (v === null)
            numRefs++;

        assumptions.push(copyFormula(v, refs));
    });

    return { as: assumptions, n: numRefs };
}

// Deep copy of formula
function copyFormula(x: Formula, refs: any[] = null): Formula {
    if (x === null)
        return null;

    var fm: Formula, lhs: Formula, rhs: Formula;

    if (x instanceof FormulaOneArg) {
        fm = copyFormula((<FormulaOneArg>x).fm, refs);

        var r: Formula;

        if (x instanceof fmExi)
            r = new fmExi(fm);

        else if (x instanceof fmUni)
            r = new fmUni(fm);

        if (refs !== null && fm === null)
            refs.push(r);

        return r;
    }

    else if (x instanceof FormulaTwoArg) {
        lhs = copyFormula((<FormulaTwoArg>x).lhs, refs);
        rhs = copyFormula((<FormulaTwoArg>x).rhs, refs);

        var r: Formula;

        if (x instanceof fmCon)
            r = new fmCon(lhs, rhs);

        else if (x instanceof fmDis)
            r = new fmDis(lhs, rhs);

        else if (x instanceof fmImp)
            r = new fmImp(lhs, rhs);

        if (refs !== null && lhs === null)
            refs.push(r);
        if (refs !== null && rhs === null)
            refs.push(r);

        return r;
    }

    else if (x instanceof fmFalsity)
        return new fmFalsity();

    else if (x instanceof fmPre) {
        var tms: Term[] = [];

        var numUnknownArgs = 0;

        if ((<fmPre>x).tms === null)
            tms = null;
        else
            (<fmPre>x).tms.forEach(v => {
                if (v === null)
                    numUnknownArgs++;

                tms.push(copyTerm(v, refs));
            });

        var r: Formula = new fmPre((<fmPre>x).id, tms);

        if (refs !== null && (<fmPre>x).id === null)
            refs.push(r);
        if (refs !== null && (<fmPre>x).tms === null)
            refs.push(r);

        for (var i = 0; i < numUnknownArgs; i++)
            refs.push(r);

        return r;
    }
};

// Deep copy of term
function copyTerm(x: Term, refs: any[] = null): Term {
    if (x === null)
        return null;

    if (x instanceof tmVar)
        return new tmVar((<tmVar>x).nat);
    else if (x instanceof tmFun) {
        var tms: Term[] = [];

        var numUnknownArgs = 0;

        if ((<tmFun>x).tms === null)
            tms = null;
        else
            (<tmFun>x).tms.forEach(v => {
                if (v === null)
                    numUnknownArgs++;

                tms.push(copyTerm(v, refs));
            });

        var t = new tmFun((<tmFun>x).id, tms);

        if (refs !== null && (<tmFun>x).id === null)
            refs.push(t);
        if (refs !== null && (<tmFun>x).tms === null)
            refs.push(t);

        for (var i = 0; i < numUnknownArgs; i++)
            refs.push(t);

        return t;
    }
}

// Check if two formulas are equal
function equalFormulas(fm1: any, fm2: any): boolean {
    if (fm1 === null || fm2 === null) {
        if (fm1 === null && fm2 === null)
            return true;
        else
            return false;
    }

    if (fm1 instanceof Array && fm2 instanceof Array) {
        if ((<Formula[]>fm1).length != (<Formula[]>fm2).length)
            return false;

        return (<Formula[]>fm1).every((v, i) => equalFormulas(v, (<Formula[]>fm2)[i]))
    }

    if (fm1.constructor.name !== fm2.constructor.name) {
        return false;
    }

    if (fm1 instanceof fmCon) {
        var fmC1: fmCon = <fmCon>fm1;
        var fmC2: fmCon = <fmCon>fm2;

        return equalFormulas(fmC1.lhs, fmC2.lhs)
            && equalFormulas(fmC1.rhs, fmC2.rhs);
    }

    else if (fm1 instanceof fmDis) {
        var fmD1: fmDis = <fmDis>fm1;
        var fmD2: fmDis = <fmDis>fm2;

        return equalFormulas(fmD1.lhs, fmD2.lhs)
            && equalFormulas(fmD1.rhs, fmD2.rhs);
    }

    else if (fm1 instanceof fmImp) {
        var fmI1: fmImp = <fmImp>fm1;
        var fmI2: fmImp = <fmImp>fm2;

        return equalFormulas(fmI1.lhs, fmI2.lhs)
            && equalFormulas(fmI1.rhs, fmI2.rhs);
    }

    else if (fm1 instanceof fmExi) {
        var fmE1: fmExi = <fmExi>fm1;
        var fmE2: fmExi = <fmExi>fm2;

        return equalFormulas(fmE1.fm, fmE2.fm);
    }

    else if (fm1 instanceof fmUni) {
        var fmU1: fmUni = <fmUni>fm1;
        var fmU2: fmUni = <fmUni>fm2

        return equalFormulas(fmU1.fm, fmU2.fm);
    }

    else if (fm1 instanceof fmFalsity) {
        return true;
    }

    else if (fm1 instanceof fmPre) {
        var fmP1: fmPre = <fmPre>fm1;
        var fmP2: fmPre = <fmPre>fm2;

        if (fmP1.id === fmP2.id && fmP1.tms === null && fmP2.tms === null)
            return true;

        if (fmP1.id !== fmP2.id || (fmP1.tms === null || fmP2.tms === null) || fmP1.tms.length != fmP2.tms.length) {
            return false;
        }

        return fmP1.tms.every(function (v, i) {
            if (equalFormulas(v, fmP2.tms[i])) {
                return true;
            }
        });
    }

    else if (fm1 instanceof tmVar) {
        var tmN1: tmVar = <tmVar>fm1;
        var tmN2: tmVar = <tmVar>fm2;

        return tmN1.nat == tmN2.nat;
    }

    else if (fm1 instanceof tmFun) {
        var tmF1: tmFun = <tmFun>fm1;
        var tmF2: tmFun = <tmFun>fm2;

        if (tmF1.id === tmF2.id && tmF1.tms === null && tmF2.tms === null)
            return true;

        if (tmF1.id != tmF2.id || (tmF1.tms === null || tmF2.tms === null) || tmF1.tms.length != tmF2.tms.length) {
            return false;
        }

        return tmF1.tms.every(function (v, i) {
            if (equalFormulas(v, tmF2.tms[i])) {
                return true;
            }
        });
    }

    else
        throw new Error("Failed to recognize formula object of type " + (typeof fm1));
}

// Recursively find inductive types without unknowns and add them to a parsed array
function findUndefInductivesWithoutUnknowns(rs: { parent: Inductive; premiseIndex: number; self?: Inductive }[], s: Inductive, p: Inductive, n: number, k: number): number {

    if (!formulaContainsUnknowns(s.goal) && !s.assumptions.some(v => {
        return formulaContainsUnknowns(v);
    })) {
        rs[n] = { parent: p, premiseIndex: k, self: s };
    }

    n++;

    s.premises.forEach((v, i) => {
        n = findUndefInductivesWithoutUnknowns(rs, v, s, n, i);
    });

    return n;
}

// Determines if a formula contains any unknowns (recursive)
function formulaContainsUnknowns(x: any): boolean {
    var r = false;

    if (x === null)
        return true;
    else if (x instanceof fmFalsity)
        return false;
    else if (x instanceof FormulaOneArg)
        return formulaContainsUnknowns((<FormulaOneArg>x).fm);
    else if (x instanceof FormulaTwoArg)
        return formulaContainsUnknowns((<FormulaTwoArg>x).lhs)
            || formulaContainsUnknowns((<FormulaTwoArg>x).rhs);

    else if (x instanceof fmPre) {
        return (<fmPre>x).id === null
            || (<fmPre>x).tms === null
            || (<fmPre>x).tms.some(v => {
                if (formulaContainsUnknowns(v))
                    return true;
            });
    }

    else if (x instanceof tmVar)
        return (<tmVar>x).nat === null;
    else if (x instanceof tmFun) {
        return (<tmFun>x).id === null
            || (<tmFun>x).tms === null
            || (<tmFun>x).tms.some(v => {
                if (formulaContainsUnknowns(v))
                    return true;
            });
    }

    else {
        console.log(x);
        throw new Error("Unexpected type received by function.");
    }
}

// Helper function to push indices of an array
function pushIndices(arr: any[], start: number, pushN: number) {
    if (start < 0 || pushN < 1)
        return;

    for (var i = arr.length - 1; i >= start; i--) {
        arr[i + pushN] = arr[i];
    }

    for (var i = start; i < start + pushN; i++)
        arr[i] = undefined;
}

// Helper function to set links between unknowns
function setLinkedUnks(linkedUnks: Unknown[][]) {
    linkedUnks.forEach((v, i) => {
        if (v.length == 2) {
            v[0].linkedTo = [v[1]];
            v[1].linkedTo = [v[0]];
        }
    });
}

// Helper function to generate constants and keep track of the counter
var newconstantSymbol = "c";
function getNewConstant(x: Inductive = null): string {
    var s = newconstantSymbol;

    var ts = getTerms(x);

    ts.forEach(t => {
        if (t instanceof tmFun) {
            if (t.id.search(/c\'+/) !== -1) {
                var numSpecialChars = t.id.split("*").length - 1;

                if (numSpecialChars > currentState.gc)
                    currentState.gc = numSpecialChars;
            }
        }
    });

    for (var i = 0; i <= currentState.gc; i++)
        s += "*";

    currentState.gc++;

    return s;
}

// Determines if a formula contains terms
function getFreeTerms(x: any, nestedQuantifiers = 0): { t: Term, nq: number }[] {
    if (x instanceof tmVar)
        return (<tmVar>x).nat >= nestedQuantifiers ? [{ t: <tmVar>x, nq: nestedQuantifiers }] : [];

    else if (x instanceof tmFun) {
        var ts1: { t: Term, nq: number }[] = [];
        var ts2: { t: Term, nq: number }[] = [];

        (<tmFun>x).tms.forEach(y => ts1.push.apply(ts1, getFreeTerms(y, nestedQuantifiers)));
        (<tmFun>x).tms.forEach(y => ts2.push.apply(ts2, getTerms(y)));

        if (ts1.length == ts2.length)
            ts1.unshift({ t: <tmFun>x, nq: nestedQuantifiers });

        return ts1;
    }

    else if (x instanceof fmPre) {
        var ts: { t: Term, nq: number }[] = [];

        (<fmPre>x).tms.forEach(y => ts.push.apply(ts, getFreeTerms(y, nestedQuantifiers)));

        return ts;
    }

    else if (x instanceof fmExi)
        return getFreeTerms((<fmExi>x).fm, nestedQuantifiers + 1);

    else if (x instanceof fmUni)
        return getFreeTerms((<fmUni>x).fm, nestedQuantifiers + 1);

    else if (x instanceof FormulaOneArg)
        return getFreeTerms((<FormulaOneArg>x).fm, nestedQuantifiers);

    else if (x instanceof FormulaTwoArg)
        return getFreeTerms((<FormulaTwoArg>x).lhs, nestedQuantifiers).concat(getFreeTerms((<FormulaTwoArg>x).rhs, nestedQuantifiers));

    else
        return [];
}

// Return terms occuring in a formula/proof
function getTerms(x: any): Term[] {
    // Formula cases - nothing to add yet - recurse further
    if (x instanceof FormulaOneArg)
        return getTerms((<FormulaOneArg>x).fm);

    else if (x instanceof FormulaTwoArg)
        return getTerms((<FormulaTwoArg>x).lhs).concat(getTerms((<FormulaTwoArg>x).rhs));

    else if (x instanceof fmPre) {
        var ts = [];

        if (x.tms !== null)
            x.tms.forEach(e => { ts.push.apply(ts, getTerms(e)) });

        return ts;
    }

    else if (x instanceof fmFalsity)
        return [];

    else if (x instanceof tmFun) {
        var ts = [];

        ts.push(<tmFun>x);

        if (x.tms !== null)
            x.tms.forEach(e => { ts.push.apply(ts, getTerms(e)) });

        return ts;
    }

    else if (x instanceof tmVar)
        return [<tmVar>x];

    else if (x instanceof Inductive) {
        var terms: Term[] = getTerms((<Inductive>x).goal);

        (<Inductive>x).premises.forEach(p => {
            getTerms(p).forEach(t => terms.push(t));
        });

        return terms;
    }

    else {
        console.log(x);
        throw new Error("Expected formula or term object.");
    }
}

// Helper function to return an identifier for the quantified variable
var variableSymbols = ["x", "y", "z", "u", "v", "w"];

function getQuantifiedVariable(n: number, formal: boolean = false): string {
    if (variableSymbols.length <= n) {
        var s = variableSymbols[variableSymbols.length - 1];

        if (formal)
            s += new String(n - variableSymbols.length)
        else
            for (var i = 0; i < n - variableSymbols.length + 1; i++)
                s += "'";

        return s;
    }
    else return variableSymbols[n];
}

// Returns the precedence of a given formula
function precedence(x: Formula): number {
    if (x instanceof fmFalsity || x instanceof fmPre)
        return 1;

    else if (x instanceof fmCon)
        return 2;

    else if (x instanceof fmDis)
        return 3;

    else if (x instanceof fmImp)
        return 4;

    else if (x instanceof fmExi || x instanceof fmUni)
        return 5;

    else
        return 0;
}

// Reconstructs lists of unknowns from parsed proof structure
function reconstructUnknownsFromProof(x: any, l: Unknown[] = [], nq: number = 0, parentSyn: Inductive = null): Unknown[] {
    if (x instanceof Inductive) {
        //
        // Now considering type: Inductive
        //

        var x: any = x;

        var p: Formula, q: Formula;

        if (x instanceof synImpE) {
            //
            // Special case: ImpE
            //

            p = x.premises[1].goal;
            var impPQ: fmImp = <fmImp>x.premises[0].goal;

            if (!equalFormulas(p, impPQ.lhs)) {
                console.log(p, impPQ.lhs);
                throw new Error("Linked formula p is different despite being linked");
            }

            if (p === null) {
                var unkQ1: Unknown = { x: x.premises[1], inFm: 1 };
                var unkQ2: Unknown = { x: impPQ, inFm: 1 };

                unkQ1.linkedTo = [unkQ2];
                unkQ2.linkedTo = [unkQ1];

                l.push(unkQ1, unkQ2);
            } else {
                var lp1 = reconstructUnknownsFromProof(p, []);
                var lp2 = reconstructUnknownsFromProof(impPQ.lhs, []);

                for (var i = 0; i < lp1.length; i++) {
                    lp1[i].linkedTo = [lp2[i]];
                    lp2[i].linkedTo = [lp1[i]];
                }

                l = l.concat(lp1.concat(lp2));
            }
        } else if (x instanceof synDisE) {
            //
            // Special case: DisE
            //

            var disPQ: fmDis = <fmDis>(<synDisE>x).premises[0].goal;
            p = disPQ.lhs;
            q = disPQ.rhs;

            var assumP: Formula[] = (<synDisE>x).premises[1].assumptions;
            var assumQ: Formula[] = (<synDisE>x).premises[2].assumptions

            var qIndex = 0,
                pIndex = 0;

            if (!assumQ.some((v, i) => { if (equalFormulas(q, v)) { qIndex = i; return true } })
                || !assumP.some((v, i) => { if (equalFormulas(p, v)) { pIndex = i; return true } })) {
                throw new Error("Linked formulas p and/or q are different despite being linked");
            }

            var lp1: Unknown[] = [], lp2: Unknown[] = [],
                lq1: Unknown[] = [], lq2: Unknown[] = [];

            var unkP1: Unknown, unkP2: Unknown,
                unkQ1: Unknown, unkQ2: Unknown;

            if (p === null) {
                unkP1 = { x: disPQ, inFm: 1 };
                unkP2 = { x: (<synDisE>x).premises[1], inAssumption: pIndex };
                unkP1.linkedTo = [unkP2];
                unkP2.linkedTo = [unkP1];

                lp1.push(unkP1);
                lp2.push(unkP2);
            } else {
                lp1 = reconstructUnknownsFromProof(p, []);
                lp2 = reconstructUnknownsFromProof(assumP[pIndex], []);

                for (var i = 0; i < lp1.length; i++) {
                    lp1[i].linkedTo = [lp2[i]];
                    lp2[i].linkedTo = [lp1[i]];
                }
            }

            if (q === null) {
                unkQ1 = { x: disPQ, inFm: 2 };
                unkQ2 = { x: (<synDisE>x).premises[2], inAssumption: qIndex };
                unkQ1.linkedTo = [unkQ2];
                unkQ2.linkedTo = [unkQ1];

                lq1.push(unkQ1);
                lq2.push(unkQ2);
            } else {
                lq1 = reconstructUnknownsFromProof(q, []);
                lq2 = reconstructUnknownsFromProof(assumQ[qIndex], []);

                for (var i = 0; i < lq1.length; i++) {
                    lq1[i].linkedTo = [lq2[i]];
                    lq2[i].linkedTo = [lq1[i]];
                }
            }

            l = l.concat(lp1.concat(lq1.concat(lp2.concat(lq2))));

        } else if (x instanceof synExiI) {
            //
            // Special case: ExiI
            //

            var fm: Formula = (<synExiI>x).premises[0].goal;

            var exiIUnknowns: Unknown[] = reconstructUnknownsFromProof(fm, [], 0, <synExiI>x);

            exiIUnknowns.forEach(u => {
                u.linkedTo = [];
            });

            exiIUnknowns.forEach(u1 => {
                exiIUnknowns.forEach(u2 => {
                    if (u1 !== u2)
                        if (u1.inFm == u2.inFm)
                            u1.linkedTo.push(u2);
                })
            });

            l = l.concat(exiIUnknowns);

        } else {
            //
            // General case
            //

            if ((<Inductive>x).goal === null)
                // Unknown is goal
                l.push({ x: x, inFm: 1 });
            else
                l = reconstructUnknownsFromProof((<Inductive>x).goal, l);

            // Unknowns in assumptions
            (<Inductive>x).assumptions.forEach((v, i) => {
                if (v === null) {
                    l.push({ x: x, inAssumption: i });
                } else {
                    l = reconstructUnknownsFromProof(v, l)
                }
            });

            // Unknowns in premises
            (<Inductive>x).premises.forEach(v => {
                l = reconstructUnknownsFromProof(v, l)
            });
        }
    }

    else if (x instanceof Formula) {
        //
        // Now considering type: Formula
        //
        if (x instanceof fmUni || x instanceof fmExi) {
            //
            // Now considering type: Quantified formula
            //

            if (x.fm === null) {
                l.push({ x: x, inFm: 1 });
            } else {
                l = reconstructUnknownsFromProof((<FormulaOneArg>x).fm, l, nq + 1, parentSyn);
            }
        }

        else if (x instanceof FormulaOneArg) {
            //
            // Now considering type: One argument formula
            //

            if ((<FormulaOneArg>x).fm === null) {
                l.push({ x: x, inFm: 1 });
            } else {
                l = reconstructUnknownsFromProof((<FormulaOneArg>x).fm, l, nq, parentSyn);
            }
        }

        else if (x instanceof FormulaTwoArg) {
            //
            // Now considering type: Two argument formula
            //

            if ((<FormulaTwoArg>x).lhs === null) {
                l.push({ x: x, inFm: 1 });
            } else {
                l = reconstructUnknownsFromProof((<FormulaTwoArg>x).lhs, l, nq, parentSyn);
            }

            if ((<FormulaTwoArg>x).rhs === null) {
                l.push({ x: x, inFm: 2 });
            } else {
                l = reconstructUnknownsFromProof((<FormulaTwoArg>x).rhs, l, nq, parentSyn);
            }
        }

        else if (x instanceof fmPre) {
            //
            // Now considering type: Predicate
            //

            if ((<fmPre>x).id === null) {
                l.push({ x: x, inFm: 1 });
            }

            if ((<fmPre>x).tms === null) {
                l.push({ x: x, inFm: 2 });
            }

            else {
                (<fmPre>x).tms.forEach((v, i) => {
                    if (v === null) {
                        l.push({ x: x, inTm: i, parent: { x: parentSyn, nq: nq } });
                    } else {
                        l = reconstructUnknownsFromProof(v, l, nq, parentSyn);
                    }
                });
            }
        }
    }

    else if (x instanceof Term) {
        //
        // Now considering type: Term
        //

        if (x instanceof tmFun) {
            //
            // Now considering type: Function
            //

            if ((<tmFun>x).id === null) {
                l.push({ x: x, inFm: 1 });
            }

            if ((<tmFun>x).tms === null) {
                l.push({ x: x, inFm: 2 });
            }

            else {
                (<tmFun>x).tms.forEach((v, i) => {
                    if (v === null) {
                        l.push({ x: x, inTm: i, parent: { x: parentSyn, nq: nq } });
                    } else {
                        l = reconstructUnknownsFromProof(v, l, nq, parentSyn = parentSyn);
                    }
                });
            }
        }

        else if (x instanceof tmVar) {
            //
            // Now considering type: Variable
            //

            if ((<tmVar>x).nat === null)
                l.push({ x: x, inFm: 1, parent: { x: parentSyn, nq: nq } });
        }
    }

    return l;
};

// Gets the Isabelle (code) syntax for a proof
function getInternalSyntaxHTML(x: any, isTerm: boolean = false, skipOutermostParentheses: boolean = false): string {

    var fmIsa: string;
    var outermostParentheses = false;

    if (x instanceof fmCon) {
        outermostParentheses = true;

        var fmC: fmCon = <fmCon>x;
        fmIsa = '<div class="con">Con</div><div class="arg">' + getInternalSyntaxHTML(fmC.lhs) + '</div><div class="arg lastArg">' + getInternalSyntaxHTML(fmC.rhs) + '</div>';
    }

    else if (x instanceof fmDis) {
        outermostParentheses = true;

        var fmD: fmDis = <fmDis>x;
        fmIsa = '<div class="dis">Dis</div><div class="arg">' + getInternalSyntaxHTML(fmD.lhs) + '</div><div class="arg lastArg">' + getInternalSyntaxHTML(fmD.rhs) + '</div>';
    }

    else if (x instanceof fmImp) {
        outermostParentheses = true;

        var fmI: fmImp = <fmImp>x;
        fmIsa = '<div class="imp">Imp</div><div class="arg">' + getInternalSyntaxHTML(fmI.lhs) + '</div><div class="arg lastArg">' + getInternalSyntaxHTML(fmI.rhs) + '</div>';
    }

    else if (x instanceof fmExi) {
        outermostParentheses = true;

        var fmE: fmExi = <fmExi>x;
        fmIsa = '<div class="exi">Exi</div><div class="arg lastArg">' + getInternalSyntaxHTML(fmE.fm) + '</div>';
    }

    else if (x instanceof fmUni) {
        outermostParentheses = true;

        var fmU: fmUni = <fmUni>x;
        fmIsa = '<div class="uni">Uni</div><div class="arg lastArg">' + getInternalSyntaxHTML(fmU.fm) + '</div>';
    }

    else if (x instanceof fmFalsity) {
        var fmF: fmFalsity = <fmFalsity>x;
        fmIsa = '<div class="falsity">Falsity</div>';
    }

    else if (x instanceof fmPre) {
        outermostParentheses = true;

        var fmP: fmPre = <fmPre>x;
        fmIsa = '<div class="pre">Pre</div><div class="arg id">' + (fmP.id === null ? '<a class=\"newID pre\" title=\"Unknown ID\">¤<\/a>' : nadeaQuot + fmP.id + nadeaQuot) + "</div>";

        fmIsa += '<div class="arg lastArg">';

        if (fmP.tms === null) {
            fmIsa += '<a class=\"newTms\" title=\"Unknown list of terms\">¤<\/a>';
        } else {
            var elems: string[] = [];

            fmP.tms.forEach(function (v) {
                elems.push(getInternalSyntaxHTML(v, true, true));
            });

            fmIsa += '<div class="leftBracket">[</div>' + elems.join('<div class="comma">,</div>') + '<div class="rightBracket">]</div>';
        }

        fmIsa += "</div>";
    }

    else if (x instanceof tmVar) {
        var tmN: tmVar = <tmVar>x;
        fmIsa = '<div class="var">Var</div><div class="arg lastArg">' + tmN.nat.toString() + "</div>";
    }

    else if (x instanceof tmFun) {
        outermostParentheses = true;

        var tmF: tmFun = <tmFun>x;
        fmIsa = '<div class="fun">Fun</div><div class="arg id">' + (tmF.id === null ? '<a class=\"newID fun\" title=\"Unknown ID\">¤<\/a>' : nadeaQuot + tmF.id + nadeaQuot) + "</div>";

        fmIsa += '<div class="arg lastArg">';

        if (tmF.tms === null) {
            fmIsa += '<a class=\"newTms\" title=\"Unknown list of terms\">¤<\/a>';
        } else {
            var elems: string[] = [];

            tmF.tms.forEach(function (v) {
                elems.push(getInternalSyntaxHTML(v, true, true));
            });

            fmIsa += '<div class="leftBracket">[</div>' + elems.join('<div class="comma">,</div>') + '<div class="rightBracket">]</div>';
        }

        fmIsa += "</div>";
    }

    else
        fmIsa = isTerm ? '<a class=\"newTm\" title=\"Unknown term\">¤<\/a>' : '<a class=\"newFormula\" title=\"Unknown formula\">¤<\/a>';

    if (outermostParentheses && !skipOutermostParentheses)
        fmIsa = '<div class="leftParentheses">(</div>' + fmIsa + '<div class="rightParentheses">)</div>';

    return fmIsa;
}

function getMaxNumNestedQuantifiers(x: Formula): number {
    if (x instanceof fmUni) {
        return getMaxNumNestedQuantifiers(x.fm) + 1;
    }

    else if (x instanceof fmExi) {
        return getMaxNumNestedQuantifiers(x.fm) + 1;
    }

    else if (x instanceof FormulaTwoArg) {
        return Math.max(getMaxNumNestedQuantifiers(x.lhs), getMaxNumNestedQuantifiers(x.rhs));
    }

    else {
        return 0;
    }
}

function getFormalSyntax(x: any, nq: number, y: any, z: Formula[]): string {
    return getFormalSyntaxAux(x, nq, y, Math.max(...z.map(f => getMaxNumNestedQuantifiers(f))));
}

// Gets the formal syntax for a proof
function getFormalSyntaxAux(x: any, nq: number, y: any, maxNq: number): string {
    // nq: number of nested quantifiers

    var fmFormal: string;

    if (x instanceof fmCon) {
        var fmC: fmCon = <fmCon>x;
        fmFormal = '<div class="arg">' + getFormalSyntaxAux(fmC.lhs, nq, fmC, maxNq) + "</div>";

        if (fmC.lhs instanceof fmCon)
            fmFormal = '<div class="leftParentheses">(</div>' + fmFormal + '<div class="rightParentheses">)</div>';

        fmFormal += '<div class="con">&and;</div><div class="arg lastArg">' + getFormalSyntaxAux(fmC.rhs, nq, fmC, maxNq) + "</div>";
    }

    else if (x instanceof fmDis) {
        var fmD: fmDis = <fmDis>x;
        fmFormal = '<div class="arg">' + getFormalSyntaxAux(fmD.lhs, nq, fmD, maxNq) + "</div>";

        if (fmD.lhs instanceof fmDis)
            fmFormal = '<div class="leftParentheses">(</div>' + fmFormal + '<div class="rightParentheses">)</div>';

        fmFormal += '<div class="dis">&or;</div><div class="arg">' + getFormalSyntaxAux(fmD.rhs, nq, fmD, maxNq) + '</div>';
    }

    else if (x instanceof fmImp) {
        var fmI: fmImp = <fmImp>x;
        fmFormal = '<div class="arg">' + getFormalSyntaxAux(fmI.lhs, nq, fmI, maxNq) + "</div>";

        if (fmI.lhs instanceof fmImp)
            fmFormal = '<div class="leftParentheses">(</div>' + fmFormal + '<div class="rightParentheses">)</div>';

        fmFormal += '<div class="imp">&rarr;</div><div class="arg">' + getFormalSyntaxAux(fmI.rhs, nq, fmI, maxNq) + "</div>";
    }

    else if (x instanceof fmExi) {
        var fmE: fmExi = <fmExi>x;

        fmFormal = '<div class="exi">&exist;' + getQuantifiedVariable(nq) + '.</div><div class="arg">' + getFormalSyntaxAux(fmE.fm, nq + 1, fmE, maxNq) + '</div>';

        if (!(y instanceof fmExi) && !(y instanceof fmUni) && precedence(x) < precedence(y))
            fmFormal = '<div class="leftParentheses">(</div>' + fmFormal + '<div class="rightParentheses">)</div>';
    }

    else if (x instanceof fmUni) {
        var fmU: fmUni = <fmUni>x;
        fmFormal = '<div class="uni">&forall;' + getQuantifiedVariable(nq) + '.</div><div class="arg">' + getFormalSyntaxAux(fmU.fm, nq + 1, fmU, maxNq) + '</div>';

        if (!(y instanceof fmExi) && !(y instanceof fmUni) && precedence(x) < precedence(y))
            fmFormal = '<div class="leftParentheses">(</div>' + fmFormal + '<div class="rightParentheses">)</div>';
    }

    else if (x instanceof fmFalsity) {
        var fmF: fmFalsity = <fmFalsity>x;
        fmFormal = '<div class="falsity">&perp;</div>';
    }

    else if (x instanceof fmPre) {
        var fmP: fmPre = <fmPre>x;
        fmFormal = '<div class="pre"><div class="id">';
        fmFormal += fmP.id === null ? '<span title="Unknown ID" class="formalUnknown">¤</span>' : fmP.id;
        fmFormal += '</div>';

        if (fmP.tms === null) {
            fmFormal += '<div class="leftParentheses">(</div><span title="Unknown list of terms" class="formalUnknown">¤</span><div class="rightParentheses">)</div>';
        } else {
            var elems: string[] = [];

            fmP.tms.forEach(function (v) {
                elems.push(getFormalSyntaxAux(v, nq, fmP, maxNq));
            });

            if (elems.length > 0)
                fmFormal += '<div class="leftParentheses">(</div>' + elems.join('<div class="comma">,</div>') + '<div class="rightParentheses">)</div>';
        }

        fmFormal += '</div>';
    }

    else if (x instanceof tmVar) {
        var tmN: tmVar = <tmVar>x;
        var qvIndex = tmN.nat + 1 > nq ? maxNq + tmN.nat - nq : nq - tmN.nat - 1;

        fmFormal = '<div class="var">' + (tmN.nat === null ? '<span title="Unknown ID" class="formalUnknown">¤</span>' : getQuantifiedVariable(qvIndex)) + '</div>';
    }

    else if (x instanceof tmFun) {
        var tmF: tmFun = <tmFun>x;
        fmFormal = '<div class="fun"><div class="id">' + (tmF.id === null ? '<span title="Unknown ID" class="formalUnknown">¤</span>' : tmF.id.replace("*", "'")) + '</div>';

        if (tmF.tms === null) {
            fmFormal += '(<span title="Unknown list of terms" class="formalUnknown">¤</span><div class="rightParentheses">)</div>';
        } else {
            var elems: string[] = [];

            tmF.tms.forEach(function (v) {
                elems.push(getFormalSyntaxAux(v, nq, tmF, maxNq));
            });

            if (elems.length > 0)
                fmFormal += '<div class="leftParentheses">(</div>' + elems.join('<div class="comma">,</div>') + '<div class="rightParentheses">)</div>';
        }

        fmFormal += '</div>';
    }

    else
        fmFormal = '<span title="Unknown formula" class="formalUnknown">¤</span>';

    if (y !== undefined && y !== null)
        if (precedence(x) > precedence(y))
            fmFormal = '<div class="leftParentheses">(</div>' + fmFormal + '<div class="rightParentheses">)</div>';

    return fmFormal;
}

// Returns the corresponding name of a rule
function getRuleHTML(x): string {
    if (x instanceof synBool)
        return "Boole";
    else if (x instanceof synConE1)
        return "Con_E1";
    else if (x instanceof synConE2)
        return "Con_E2";
    else if (x instanceof synConI)
        return "Con_I";
    else if (x instanceof synDisE)
        return "Dis_E";
    else if (x instanceof synDisI1)
        return "Dis_I1";
    else if (x instanceof synDisI2)
        return "Dis_I2";
    else if (x instanceof synExiI)
        return "Exi_I";
    else if (x instanceof synExiE) {
        if ((<synExiE>x).waitingForPCompletion)
            return '<span title="Complete definition of unknown formula p to generate remaining premises.">Exi_E (!)</span>';
        else if (!(<synExiE>x).cIsNew)
            return '<span title="Introduced function symbol is not new. Please choose a new function symbol." class="error">Exi_E (!)</span>';
        else
            return "Exi_E";
    } else if (x instanceof synImpE)
        return "Imp_E";
    else if (x instanceof synImpI)
        return "Imp_I";
    else if (x instanceof synUniE)
        return ((<synUniE>x).waitingForTermSelection ? '<a title="Complete selection of terms to quantify." class="selectTerms">Uni_E (!)</a>' : "Uni_E");
    else if (x instanceof synUniI)
        return ((<synUniI>x).cIsNew === false ? '<span title="Introduced function symbol is not new. Please choose a new function symbol." class="error">Uni_I (!)</span>' : "Uni_I");
    else if (x instanceof Inductive) {
        if ((<Inductive>x).trueByAssumption)
            return '<span title="Goal is in list of assumptions.">Assume</span>';
        else
            return "<a class='newSynRule' title='Unknown rule'>¤</a>";
    }
    else {
        console.log(x);
        throw new Error("Expected (sub-)class of Inductive");
    }
}

// Generate Isabelle file
function generateIsabelleFile(i: Inductive) {
    var isaCode: string = 'theory Scratch imports Main begin\n\n';

    if (i.goal !== null) {
        isaCode += 'lemma "' + i.goal.getIsabelleFormula(0) + '"\n'
        isaCode += i.getIsabelleProof(0);
    }

    isaCode += '\nend';

    return isaCode;
}

// Attach key bindings to application
function attachKeyBindings() {
    $(document).keydown((e) => {
        if ($(".overlay").length > 0) {
            if (e.keyCode == 27) {
                closeTopOverlay();
            }

            return;
        }

        if (e.keyCode == 46) {
            stateStack.update(IbStackEvent.DELETE);

            setCurrentState(stateStack.top());
            update();
        } // delete

        else if (e.keyCode == 45) {
            stateStack.update(IbStackEvent.INSERT);
            updateHeader();
        } // insert
    });
}

function setCurrentState(s: State) {
    currentState = s;
}

// Returns the highest number of asterixes found in the proof
function getNumGeneratedConstants(x: Inductive): number {
    var n = 0;

    if (x instanceof synUniI)
        n++;

    x.premises.forEach(v => {
        n += getNumGeneratedConstants(v);
    });

    return n;
}

//
// UNDO BLOCK
//

enum IbStackEvent {
    DELETE,
    INSERT,
    UPDATE,
    UPDATE_INTERNAL
}

class IbStack {
    stack: State[];
    markedIndex: number;

    constructor(s: State) {
        this.reset(s);
    }

    update(e: IbStackEvent, s: State = null) {
        if (e == IbStackEvent.INSERT) {
            this.markedIndex = null;

            return;
        }

        else if (e == IbStackEvent.DELETE && (this.stack.length <= 1 || this.markedIndex == 0)) {
            return;
        }

        else {
            if (e == IbStackEvent.DELETE) {
                if (this.markedIndex !== null)
                    this.markedIndex--;
                else
                    this.markedIndex = this.stack.length - 2;

                this.stack.push(copyState(this.stack[this.markedIndex]));
            }

            else {
                if (s == null)
                    throw new Error();

                this.markedIndex = null;

                // On update the current state is kept as top,
                // instead the "previous" step is pushed to second last position
                if (e == IbStackEvent.UPDATE) {
                    this.stack.push(this.top());
                    this.stack[this.stack.length - 2] = s;
                } else {
                    this.stack.push(s);
                }
            }
        }
    }

    top() {
        return this.stack[this.stack.length - 1];
    }

    reset(s: State) {
        this.stack = [s];
        this.markedIndex = null;
    }
};

function prepareCurrentStateUpdate() {
    var s = copyState(currentState);

    stateStack.update(IbStackEvent.UPDATE, s);
}

function copyState(s: State): State {
    var x: State = new State;

    var refs = [];
    var ltIndices: number[][] = []

    x.p = copyInductive(s.p, refs);

    x.xs = [];
    s.xs.forEach((e, i) => x.xs[i] = copyUnknown(e, refs[i], s.xs, ltIndices));

    ltIndices.forEach((lts, i) => {
        lts.forEach(j => {
            x.xs[i].linkedTo.push(x.xs[j]);
        });
    });

    x.gc = s.gc;

    return x;
}

function copyInductive(x, refs: any[]): Inductive {
    var i: Inductive;

    // Copy
    var g = copyFormula(x.goal, refs);
    var cpas = copyAssumptions(x, refs);

    // Inst. new object of same type
    if (x instanceof synBool) {
        i = new synBool(g, cpas.as);
    }

    else if (x instanceof synConE1) {
        i = new synConE1(g, cpas.as);
    }

    else if (x instanceof synConE2) {
        i = new synConE2(g, cpas.as);
    }

    else if (x instanceof synConI) {
        i = new synConI(g, cpas.as);
    }

    else if (x instanceof synDisE) {
        i = new synDisE(g, cpas.as);
    }

    else if (x instanceof synDisI1) {
        i = new synDisI1(g, cpas.as);
    }

    else if (x instanceof synDisI2) {
        i = new synDisI2(g, cpas.as);
    }

    else if (x instanceof synExiE) {
        i = new synExiE(g, cpas.as);

        (<synExiE>i).c = (<synExiE>x).c;
        (<synExiE>i).cIsNew = (<synExiE>x).cIsNew;
        (<synExiE>i).waitingForPCompletion = (<synExiE>x).waitingForPCompletion;
    }

    else if (x instanceof synExiI) {
        i = new synExiI(g, cpas.as);
    }

    else if (x instanceof synUniE) {
        i = new synUniE(g, cpas.as);

        (<synUniE>i).waitingForTermSelection = (<synUniE>x).waitingForTermSelection;
    }

    else if (x instanceof synUniI) {
        i = new synUniI(g, cpas.as);

        (<synUniI>i).c = (<synUniI>x).c;
        (<synUniI>i).cIsNew = (<synUniI>x).cIsNew;
    }

    else if (x instanceof synImpE) {
        i = new synImpE(g, cpas.as);
    }

    else if (x instanceof synImpI) {
        i = new synImpI(g, cpas.as);
    }

    else {
        i = new Inductive(g, cpas.as);
    }

    if (g === null) {
        // Goal is unknown
        refs.push(i);
    }

    for (var j = 0; j < cpas.n; j++)
        refs.push(i);

    var ps = [];
    x.premises.forEach(i => ps.push(copyInductive(i, refs)));
    i.premises = ps;

    return i;
}

function copyUnknown(x: Unknown, ref: any, xs: Unknown[], ltIndices: number[][]): Unknown {
    var u: Unknown = { x: ref };

    if (x.inAssumption !== undefined)
        u.inAssumption = x.inAssumption;

    if (x.inFm !== undefined)
        u.inFm = x.inFm;

    if (x.inTm !== undefined)
        u.inTm = x.inTm;

    var lts: number[] = [];

    if (x.linkedTo !== undefined) {
        u.linkedTo = [];

        x.linkedTo.forEach((u, i) => {
            var z = xs.indexOf(u);

            if (z !== -1)
                lts.push(z);
        });
    }

    ltIndices.push(lts);

    return u;
}

//
// END OF UNDO
//

function countUnknowns(x: any): number {
    if (x === null)
        return 1;

    if (x instanceof Array) {
        var r = 0;

        (<any[]>x).forEach(y => r += countUnknowns(y));

        return r;
    }


    if (x instanceof FormulaOneArg) {
        return countUnknowns((<FormulaOneArg>x).fm);
    }

    else if (x instanceof FormulaTwoArg) {
        return countUnknowns((<FormulaTwoArg>x).lhs) + countUnknowns((<FormulaTwoArg>x).rhs);
    }

    else if (x instanceof fmPre) {
        var r = countUnknowns((<fmPre>x).id);

        r += countUnknowns((<fmPre>x).tms);

        return r;
    }

    else if (x instanceof tmFun) {
        var r = countUnknowns((<tmFun>x).id);

        r += countUnknowns((<tmFun>x).tms);

        return r;
    }

    else if (x instanceof Inductive) {
        var r = countUnknowns((<Inductive>x).goal);
        (<Inductive>x).assumptions.forEach(a => r += countUnknowns(a));

        var x: any = x;

        if (r == 0
            && !(<Inductive>x).trueByAssumption
            && !(x instanceof synBool
                || x instanceof synConE1
                || x instanceof synConE2
                || x instanceof synConI
                || x instanceof synDisE
                || x instanceof synDisI1
                || x instanceof synDisI2
                || x instanceof synImpE
                || x instanceof synImpI
                || x instanceof synExiE
                || x instanceof synExiI
                || x instanceof synUniE
                || x instanceof synUniI)) {
            r += 1;
        }

        (<Inductive>x).premises.forEach(p => r += countUnknowns(p));

        return r;
    }

    else {
        return 0;
    }
}

function countNoProofRules(x: Inductive): number {
    return x.premises.length > 0 ? 1 + x.premises.map<number>(v => countNoProofRules(v)).reduce((a, b) => a + b) : 0;
}

//
// Prover section
//

enum ProofLineStatus {
    Incomplete = 0,
    WaitingForProver = 1,
    Provable = 3,
    TimedOut = 4
}


class WorkerQueue {
    MAX_NUM_WORKERS = 3;
    MAX_WORKER_TIME = 5000;
    waitingWorkers: { w: Worker, x: Formula, assumptions: Formula[] }[] = [];
    runningWorkers = 0;
    provedFormulas: ProvedFormulas;

    setProvedFormulas(provedFormulas) {
        this.provedFormulas = provedFormulas;
    }

    workerDone() {
        this.runningWorkers -= 1;

        if (this.waitingWorkers.length > 0 && this.runningWorkers < this.MAX_NUM_WORKERS) {
            var y = this.waitingWorkers.shift();

            this.startWorker(y.w, y.x, y.assumptions);
        }

        if (this.waitingWorkers.length == 0)
            updateProofLineStatus();
    }

    addToQueue(w: Worker, x: Formula, assumptions: Formula[]) {
        if (this.runningWorkers < this.MAX_NUM_WORKERS) {
            this.startWorker(w, x, assumptions);
        }

        else {
            this.waitingWorkers.push({ w: w, x: x, assumptions: assumptions });
        }
    }

    startWorker(w: Worker, x: Formula, assumptions: Formula[]) {
        var to: number;

        w.onmessage = e => {
            this.provedFormulas.addFormula(x, assumptions, ProofLineStatus.Provable);
            clearTimeout(to);
            this.workerDone();
        };

        w.postMessage({ formula: formulaToString(assumptionsToImp(assumptions, x)) });
        this.runningWorkers += 1;

        to = setTimeout(() => {
            // Web worker timeout
            this.provedFormulas.addFormula(x, assumptions, ProofLineStatus.TimedOut);
            w.terminate();
            w = undefined;
            this.workerDone();
        }, this.MAX_WORKER_TIME);
    }
}

class ProvedFormulas {
    formulas: { formula: Formula, provability: { assumptions: Formula[], proofLineStatus: ProofLineStatus }[] }[];
    workerQueue: WorkerQueue;

    constructor(wq: WorkerQueue) {
        this.formulas = [];
        this.workerQueue = wq;
    }

    getProofLineStatus(x: Formula, assumptions: Formula[]): ProofLineStatus {
        var truthValue = this.getFormulaProvability(x, assumptions);

        if (truthValue !== null)
            return truthValue;

        var worker = new Worker("worker.js");

        var to: number;

        this.workerQueue.addToQueue(worker, x, assumptions)

        return ProofLineStatus.WaitingForProver;
    }

    getFormulaProvability(x: Formula, assumptions: Formula[]): ProofLineStatus {
        var r: ProofLineStatus = null;

        this.formulas.forEach((y, i) => {
            if (equalFormulas(y.formula, x)) {
                y.provability.forEach((z, j) => {
                    if (z.assumptions.every(a => assumptions.some(b => equalFormulas(a, b)))) {
                        r = z.proofLineStatus;
                        return true;
                    }
                });

                return true;
            }
        });

        return r;
    }

    addFormula(x: Formula, assumptions: Formula[], y: ProofLineStatus): void {
        if (this.getFormulaProvability(x, assumptions) !== null)
            return;

        var fmIndex = -1;

        this.formulas.forEach((y, i) => {
            if (equalFormulas(y.formula, x)) {
                fmIndex = i;
                return true;
            }
        });

        if (fmIndex == -1) {
            this.formulas.push({ formula: x, provability: [{ assumptions: assumptions, proofLineStatus: y }] });
        } else {
            this.formulas[fmIndex].provability.push({ assumptions: assumptions, proofLineStatus: y });
        }
    }
}

var workerQueue = new WorkerQueue();
var provedFormulas = new ProvedFormulas(workerQueue);
workerQueue.setProvedFormulas(provedFormulas)

function assumptionsToImp(a: Formula[], x: Formula): Formula {
    if (a.length == 0)
        return x;

    var nextResult = new fmImp(null, null);
    var result = nextResult;
    var prevResult;

    a.forEach(v => {
        nextResult.lhs = v;
        nextResult.rhs = new fmImp(null, null);

        prevResult = nextResult;

        nextResult = (<fmImp>prevResult.rhs);
    });

    prevResult.rhs = x;

    return result;
}

function getProverData(x: Inductive): { linesStatus: ProofLineStatus[], n: number } {
    var linesStatus: ProofLineStatus[] = [];
    var i = 0;

    if (countUnknowns(x.assumptions) > 0 || countUnknowns(x.goal) > 0) {
        // Unknowns. Cannot run prover.
        linesStatus[i] = ProofLineStatus.Incomplete;

        i += 1;

        var j = i;
    } else {
        var j = i + 1;

        linesStatus[i] = null;

        x.premises.forEach(v => {
            var premiseResult = getProverData(v);

            linesStatus.push.apply(linesStatus, premiseResult.linesStatus);

            j += premiseResult.n;
        });

        if (x.trueByAssumption || x.premises.length > 0 && linesStatus.slice(i + 1, j).every(v => v === ProofLineStatus.Provable)) {
            linesStatus[i] = ProofLineStatus.Provable;
            provedFormulas.addFormula(x.goal, x.assumptions, ProofLineStatus.Provable);
        }
        else
            linesStatus[i] = provedFormulas.getProofLineStatus(x.goal, x.assumptions);
    }

    return {
        linesStatus: linesStatus,
        n: j
    }
}

var proverData: ProofLineStatus[];
function updateProofLineStatus() {
    proverData = getProverData(currentState.p).linesStatus;

    var x = 0;

    $(".line").each((i, e) => {
        if ($(".middle", e).html() == "*") {
            x += 1;
            return true;
        }

        switch (proverData[i - x]) {
            case ProofLineStatus.TimedOut:
                $(".lineNumber", e).css({ color: "orange" }).attr("title", "Goal could not be proved.");
                break;
            case ProofLineStatus.Provable:
                $(".lineNumber", e).css({ color: "" }).attr("title", "");
                break;
            case ProofLineStatus.WaitingForProver:
                $(".lineNumber", e).css({ color: "" }).attr("title", "Waiting for prover.");
                break;
            case ProofLineStatus.Incomplete:
                $(".lineNumber", e).css({ color: "" }).attr("title", "Unknowns - cannot run prover.");
                break;
            default:
                console.log("Unexpected type.", proverData[i - x], i - x, proverData);
                throw new Error("Unexpected LineStatus type");
        }
    });
}

function formulaToString(x: Formula): string {
    return formulaToStringAux(x, 0, getMaxNumNestedQuantifiers(x));
}

function formulaToStringAux(x: Formula | Term, nq: number, maxNq: number): string {
    if (x instanceof fmExi) {
        return "(exists  " + getQuantifiedVariable(nq) + ". " + formulaToStringAux(x.fm, nq + 1, maxNq) + " )";
    }

    else if (x instanceof fmUni) {
        return "(forall  " + getQuantifiedVariable(nq) + ". " + formulaToStringAux(x.fm, nq + 1, maxNq) + " )";
    }

    else if (x instanceof fmCon) {
        return "(" + formulaToStringAux(x.lhs, nq, maxNq) + " /\\ " + formulaToStringAux(x.rhs, nq, maxNq) + ")";
    }

    else if (x instanceof fmDis) {
        return "(" + formulaToStringAux(x.lhs, nq, maxNq) + " \\/ " + formulaToStringAux(x.rhs, nq, maxNq) + ")";
    }

    else if (x instanceof fmImp) {
        return "(" + formulaToStringAux(x.lhs, nq, maxNq) + " ==> " + formulaToStringAux(x.rhs, nq, maxNq) + ")";
    }

    else if (x instanceof fmPre) {
        return x.id.replace("*", "'") + "(" + x.tms.map(v => formulaToStringAux(v, nq, maxNq)).join(", ") + ")";
    }

    else if (x instanceof tmFun) {
        return x.id.replace("*", "'") + (x.tms.length == 0 ? "" : "(" + x.tms.map(v => formulaToStringAux(v, nq, maxNq)).join(", ") + ")");
    }

    else if (x instanceof tmVar) {
        return getQuantifiedVariable(x.nat + 1 > nq ? maxNq + x.nat - nq : nq - x.nat - 1)
    }

    else if (x instanceof fmFalsity) {
        return "false";
    }

    else {
        console.log(x);
        throw new Error("Could not recognize formula/term type.");
    }

}