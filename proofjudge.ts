/// <reference path="references.d.ts" />

// Enumeration of user types including offline status/
enum UserType {
    OFFLINE = 0,
    STUDENT = 1,
    TEACHER = 2,
    ASSISTANT = 3,
    ADMIN = 4
}

// Global user variable
var loggedInUser: { name?: string, accessRights: UserType } = {
    accessRights: UserType.OFFLINE
};

function updateLoginData(user: { name?: string, accessRights: UserType }) {
    loggedInUser = user;
    
    if (user.accessRights == UserType.OFFLINE) {
        $(".proofjudgeBtn").html("ProofJudge Login");
    } else {
        $(".proofjudgeBtn").html("ProofJudge Update");
    }
}

function handleCommonErrors(error: number) {
    switch (error) {
        case 0:
            // Lost login session

            customDialog("You have been logged off. Save your data and login again!", false);

            break;
    }
}

function customDialog(text: string, isConfirm: boolean = false, onAccept: () => void = () => { }) {
    $(".customDialog").remove();

    var dialog = $('<div class="customDialog overlay centerPage topOfPage"></div>');

    // Position overlay at position of clicked element
    dialog.css({
        width: "250px",
        height: "100px"
    });

    dialog.append('<div class="pre">' + text + '</div>');
    dialog.append('<div>&nbsp;</div>');

    if (isConfirm) {
        dialog.append('<div style="display: inline-block; width: 50%; text-align: center;"><input id="accept" type="button" value="OK" /></div>');
        dialog.append('<div style="display: inline-block; width: 50%; text-align: center;"><input id="cancel" type="button" value="Cancel" /></div>');
    } else {
        dialog.append('<div style="text-align: center;"><input id="ok" type="button" value="OK" /></div>');
    }

    $("body").append(dialog);

    $("#accept", dialog).click(() => { dialog.remove(); onAccept(); });
    $("#cancel, #ok", dialog).click(() => { dialog.remove(); });
}

/**
 * Get user type through ajax
 */
var ajaxSettings: JQueryAjaxSettings = {
    url: "proofjudge.php",
    type: "POST",
    data: {
        action: "get_login_data"
    },
    dataType: "json",
    error: function (err) {
        console.log("Failed to get user data", err);
        updateLoginData({ accessRights: UserType.OFFLINE });
    },
    success: function (s) {
        if (s.status === "success") {
            updateLoginData({ name: s.username, accessRights: s.accessRights });
        } else {
            handleCommonErrors(s.error);
        }
    }
};

/**
 * Add proofjudge button to page layout
 */
$(document).ready(() => {
    // Add proofjudge button
    var proofJudgeBtn = $('<div class="proofjudgeBtn button big">ProofJudge</div>');

    $("#rightbar .proofjudge").append(proofJudgeBtn);

    proofJudgeBtn.click(e => proofJudgeOverlay());

    $.ajax(ajaxSettings);
});


/**
 * Status line for logged in users
 */
function statusLine() {
    if (loggedInUser.accessRights === UserType.OFFLINE)
        return null;

    var sl = $('<div class="status table"></div>');
    var tr = $('<div class="tableRow"></div>');
    sl.append(tr);

    tr.append('<div class="tableCell">Logged in as <strong>' + loggedInUser.name + '</strong></div>');
    var td = $('<div class="tableCell"></div></div>');
    tr.append(td);

    var logoutLink = $('<a class="logoutBtn">Logout</a>');

    td.append(logoutLink);

    logoutLink.on("click", e => {
        $.ajax({
            url: "proofjudge.php",
            type: "POST",
            data: {
                action: "logout"
            },
            dataType: "json",
            error: function (err) {
                console.log("Server not responding", err);
            },
            success: function (s) {
                updateLoginData({ accessRights: UserType.OFFLINE });
                $(".closeCenteredOverlay").click();
            }
        });
    });

    return sl;
}

/**
 * ProofJudge overlay
 */
function proofJudgeOverlay(): void {

    setTitle("ProofJudge");

    var outer = $("<div class=\"centeredOverlayOuter\"></div>");

    var contentOuter = $("<div class=\"overlay proofjudge\"></div>");
    var contentFlex = $("<div class=\"flexContentY\"></div>");
    var content = $("<div class=\"proofjudgeContent\"></div>");

    contentOuter.hide();
    contentOuter.append(contentFlex);
    contentFlex.append(content);

    outer.append(contentOuter);
    $("body").append(outer);

    switch (loggedInUser.accessRights) {
        case UserType.OFFLINE:
            //
            // Login page
            //

            content.append('<form id="loginArea"><div class="table"><div class="tableRow"><div class="tableCell">Username:</div><div class="tableCell"><input type="text" class="proofJudgeInputText" name="username" /></div></div><div class="tableRow"><div class="tableCell">Password:</div><div class="tableCell"><input type="password" class="proofJudgeInputText" name="password" /></div></div><div class="tableRow"><div class="tableCell"></div><div class="tableCell"><div class="floatRight"><input type="button" value="Cancel" />&nbsp;<input type="submit" value="Login" /></div></div></div></div></form>');

            // Login through ajax
            $("#loginArea").on("submit", e => {
                $.ajax({
                    url: "proofjudge.php",
                    type: "POST",
                    data: {
                        action: "authenticate_login",
                        username: $("#loginArea input[name='username']").val(),
                        password: $("#loginArea input[name='password']").val()
                    },
                    dataType: "json",
                    error: function (err) {
                        console.log("Failed to authenticate login", err);
                        updateLoginData({ accessRights: UserType.OFFLINE });
                    },
                    success: function (s) {
                        if (s.status === "success") {
                            updateLoginData({ name: s.username, accessRights: s.accessRights });

                            $(".closeCenteredOverlay", contentOuter).click();
                            proofJudgeOverlay();

                        } else {
                            handleCommonErrors(s.error);

                            switch (s.error) {
                                case 1:
                                    // Bad login data

                                    customDialog("Username/password not correct", false);

                                    break;
                            }
                        }

                    }
                });

                return false;
            });

            $("#loginArea input[type='button']").click(e => $(".closeCenteredOverlay", contentOuter).click());

            break;
        case UserType.STUDENT:
            //
            // Student page
            //

            contentFlex.prepend(statusLine());

            var table = $('<div class="table fullWidth"></div>');
            var tableRow = $('<div class="tableRow"></div>');
            var leftColumn = $('<div class="tableCell halfOfTableWidth"></div>');
            var rightColumn = $('<div class="tableCell"></div>');

            table.append(tableRow);
            tableRow.append(leftColumn);
            tableRow.append('<div class="tableCell">&nbsp;</div>');
            tableRow.append(rightColumn);
            content.append(table);

            var draftProofIDs = [];
            var draftProofs = [];

            // List of assignments
            var assignmentTable = $('<div class="table bordered"></div>');

            function dropdownDraftSelector(exerciseID: number, proofCode: String, selectedDraftID: number = null): JQuery {
                var dropdown = $('<select id="selectSolution_' + exerciseID + '"></select>');
                dropdown.append('<option value="0">-</option>');

                draftProofIDs.forEach(d => {
                    dropdown.append('<option value="' + d + '">' + draftProofs[d].name + '</option>');
                });

                dropdown.on("change", e => {
                    $.ajax({
                        url: "proofjudge.php",
                        type: "POST",
                        data: {
                            action: "submit_handin",
                            draftID: $(e.currentTarget).val(),
                            exerciseID: exerciseID
                        },
                        dataType: "json",
                        contentType: "application/x-www-form-urlencoded; charset:ISO-8859-1",
                        error: function (err) {
                            console.log("Failed to submit handin.", err);
                        },
                        success: function (s) {
                            if (s.status === "success") {
                                getDraftTable();
                            } else {
                                handleCommonErrors(s.error);

                                switch (s.error) {
                                    case 1:
                                        // Selected draft not found
                                        customDialog("Selected draft could not be found.");
                                        break;
                                    case 2:
                                        // Exercise not found, or assignment is inactive
                                        customDialog("The exercise is either from an inactive assignment, or is not assigned to logged in student.");
                                        break;
                                }
                            }
                        }

                    });
                });

                if (selectedDraftID != null)
                    dropdown.val(selectedDraftID.toString());

                return dropdown;
            }

            function getAssignmentTable() {
                assignmentTable.children().remove();

                $.ajax({
                    url: "proofjudge.php",
                    type: "POST",
                    data: {
                        action: "get_student_assignment_table"
                    },
                    dataType: "json",
                    contentType: "application/x-www-form-urlencoded; charset:ISO-8859-1",
                    error: function (err) {
                        console.log("Failed to read assignment data for student", err);
                    },
                    success: function (s) {
                        if (s.status === "success") {
                            $.each(s.table, (a_id, a) => {
                                assignmentTable.append('<div class="tableRow dark"><div class="tableCell"><strong>' + a.name + '</strong></div><div class="tableCell">Goal</div><div class="tableCell">Selected solution</div></div>');

                                var eCount = 0;
                                $.each(a.exercises, (e_id, e) => {
                                    eCount++;

                                    var tr = $('<div class="tableRow"></div>')

                                    tr.append('<div class="tableCell">Exercise ' + eCount + '</div><div class="tableCell smallFont">' + e.goal + '</div><div class="tableCell"></div>');
                                    $("div.tableCell:eq(2)", tr).append(dropdownDraftSelector(e_id, e.goal, e.handin_draft_id));

                                    assignmentTable.append(tr);
                                });
                            });
                        } else {
                            handleCommonErrors(s.error);
                        }
                    }

                });
            }

            leftColumn.append(assignmentTable);
            leftColumn.append("<br />");

            // List of drafts

            var draftTable = $('<div class="table bordered"></div>');

            function getDraftTable() {
                draftTable.children().remove();

                // Current drafts
                draftTable.append('<div class="tableRow dark"><div class="tableCell">Draft</div><div class="tableCell">Goal</div><div class="tableCell">No. of ¤</div><div class="tableCell">No. of proof rules used</div><div class="tableCell"></div><div class="tableCell"></div></div>');

                $.ajax({
                    url: "proofjudge.php",
                    type: "POST",
                    data: {
                        action: "get_draft_table"
                    },
                    dataType: "json",
                    error: function (err) {
                        console.log("Failed to read draft data for student", err);
                    },
                    success: function (s) {
                        if (s.status === "success") {
                            draftProofIDs = [];
                            draftProofs = [];

                            $.each(s.table, (d_id, d) => {
                                draftProofIDs.push(d_id);
                                draftProofs[d_id] = { name: d.name, proofObject: decodeProof(d.proofCode) };

                                var tr = $('<div class="tableRow"><div class="tableCell">' + d.name + '</div><div class="tableCell formalSyntax">' + getFormalSyntax(draftProofs[d_id].proofObject[0].goal, 0, null, [draftProofs[d_id].proofObject[0].goal]) + '</div><div class="tableCell alignRight">' + countUnknowns(draftProofs[d_id].proofObject[0]) + '</div><div class="tableCell alignRight">' + countNoProofRules(draftProofs[d_id].proofObject[0]) + '</div><div class="tableCell loadDraft"><a>Load draft</a></div><div class="tableCell deleteDraft"></div></div>');

                                draftTable.append(tr);

                                replaceFormalSymbols(tr, [{ s: /@fm/g, r: "<span class='formalUnknown'>¤</span>" }]);

                                $(".loadDraft", tr).click(e => {
                                    if (draftProofs[d_id].proofObject === null) {
                                        customDialog("The proof code is invalid and could not be loaded.");
                                    } else {
                                        customDialog("You will lose any unsaved work during load.", true, () => {
                                            loadProof(draftProofs[d_id].proofObject);
                                            $(".closeCenteredOverlay", contentOuter).click();
                                        });
                                    }
                                });

                                if (d.locked) {
                                    $(".deleteDraft", tr).html('<div title="Draft is used as handin, and cannot be deleted.">-</div>');
                                } else {
                                    $(".deleteDraft", tr).html("<a>x</a>").click(e => {
                                        customDialog("The draft cannot be recovered once deleted.\n\nDo you wish to continue?", true, () => {
                                            $.ajax({
                                                url: "proofjudge.php",
                                                type: "POST",
                                                data: {
                                                    action: "delete_draft",
                                                    draftID: d_id
                                                },
                                                dataType: "json",
                                                error: function (err) {
                                                    console.log("Failed to delete draft", err);
                                                },
                                                success: function (s) {
                                                    if (s.status === "success") {
                                                        getDraftTable();
                                                    } else {
                                                        handleCommonErrors(s.error);

                                                        switch (s.error) {
                                                            case 1:
                                                                // Selected draft not found
                                                                customDialog("Draft could not be deleted.");
                                                                break;
                                                        }
                                                    }
                                                }
                                            });
                                        });
                                    });
                                }
                            });

                            // Setup assignment table now that all drafts are loaded
                            getAssignmentTable();
                        } else {
                            handleCommonErrors(s.error);
                        }
                    }
                });
            }

            getDraftTable();

            leftColumn.append(draftTable);
            leftColumn.append("<br />");

            // Save current solution as new draft
            var saveDraftForm = $('<form id="draftForm"></form>');
            var saveDraftTable = $('<div class="table"></div>');
            saveDraftForm.append(saveDraftTable);

            saveDraftTable.append('<div class="tableCaption textline dark"><strong>Create draft of current proof state:</strong></div>');
            saveDraftTable.append('<div class="tableRow"><div class="tableCell">Draft name</div><div class="tableCell"><input type="text" class="proofJudgeInputText" name="draftName" maxlength="64" /></div></div');

            var draftGoalDiv = $('<div class="tableRow"><div class="tableCell">Goal:</div><div class="tableCell alignRight">' + getFormalSyntax(currentState.p.goal, 0, null, [...currentState.p.assumptions, currentState.p.goal]) + '</div></div');

            saveDraftTable.append(draftGoalDiv);
            saveDraftTable.append('<div class="tableRow"><div class="tableCell">No. of <span class="formalUnknown">¤</span>:</div><div class="tableCell alignRight">' + countUnknowns(currentState.p) + ' </div></div');
            saveDraftTable.append('<div class="tableRow"><div class="tableCell">No. of proof rules used:</div><div class="tableCell alignRight">' + countNoProofRules(currentState.p) + '</div></div');
            saveDraftTable.append('<div class="tableRow"><div class="tableCell"></div><div class="tableCell alignRight"><input type="submit" value="Save draft" style="width: 4.5vw; text-align: center;" /></div></div');

            replaceFormalSymbols(draftGoalDiv, [{ s: /@fm/g, r: "<span class='formalUnknown'>¤</span>" }]);

            rightColumn.append(saveDraftForm);

            $(saveDraftForm).on("submit", e => {
                $.ajax({
                    url: "proofjudge.php",
                    type: "POST",
                    data: {
                        action: "submit_draft",
                        draftName: $('input[name="draftName"]', saveDraftForm).val(),
                        proofCode: encodeProof(currentState.p)
                    },
                    dataType: "json",
                    error: function (err) {
                        console.log("Failed to submit draft", err);
                    },
                    success: function (s) {
                        if (s.status === "success") {
                            $('input[name="draftName"]').val("");

                            $('input[type="submit"]', saveDraftForm).attr("Value", "Saving...");
                            $('input[type="submit"]', saveDraftForm).attr("disabled", "disabled");

                            setTimeout(() => {
                                $('input[type="submit"]', saveDraftForm).attr("Value", "Save draft");
                                $('input[type="submit"]', saveDraftForm).removeAttr("disabled");
                                getDraftTable();
                            }, 1250);

                        } else {
                            handleCommonErrors(s.error);

                            switch (s.error) {
                                case 1:
                                    customDialog("Please provide a draft name.", false);

                                    break;
                                case 2:
                                    customDialog("Could not fetch proof code.", false);

                                    break;
                                case 3:
                                    customDialog("You already have the maximum number of allowed drafts.", false);

                                    break;
                            }
                        }
                    }
                });

                return false;
            });

            break;
        case UserType.ASSISTANT:
            //
            // Assistant page
            //

            contentFlex.prepend(statusLine());

            var tableGroup = $('<div class="table bordered fullWidth"></div>');

            $.ajax({
                url: "proofjudge.php",
                type: "POST",
                data: {
                    action: "get_assistant_assignment_solution_table"
                },
                dataType: "json",
                error: function (err) {
                    console.log("Failed get assistant assignment solution table.", err);
                },
                success: function (s) {
                    if (s.status === "success") {
                        // Header with assignment name
                        content.append('<div class="textline">' + s.assignmentName + (s.assignmentActive ? '' : ' [Inactive] ') + '</div>');

                        var numStudents = 0;

                        $.each(s.students, (student_index, student) => {
                            numStudents++;
                        });

                        var numHandinsExercises = [];

                        var decodedExercises = [];
                        var decodedHandins = [];

                        $.each(s.exercises, (exercise_index, exercise) => {
                            numHandinsExercises[exercise_index] = 0;
                            decodedExercises[exercise_index] = decodeProof(exercise);
                            decodedHandins[exercise_index] = [];

                            $.each(s.students, (student_index, student) => {
                                $.each(s.handins, (student_index2, student_handins) => {
                                    if (student_index2 == student_index) {
                                        $.each(student_handins, (exercise_index2, handin2) => {
                                            if (exercise_index == exercise_index2) {
                                                numHandinsExercises[exercise_index]++;
                                                decodedHandins[exercise_index][student_index] = decodeProof(handin2);
                                            }
                                        });
                                    }
                                });
                            });
                        });

                        function getFeedbackIcon(exercise_index, student_index) {
                            if (decodedExercises[exercise_index] === null)
                                return "Invalid exercise proof code";

                            if (decodedHandins[exercise_index][student_index] === undefined)
                                return "Handin missing";

                            if (decodedHandins[exercise_index][student_index] === null)
                                return "Invalid handin proof code";

                            if (!equalFormulas(decodedHandins[exercise_index][student_index][0].goal, decodedExercises[exercise_index][0].goal))
                                return "Wrong goal";

                            if (countUnknowns(decodedHandins[exercise_index][student_index][0].goal) === 0)
                                return "Is a solution";

                            return "Partial solution";
                        }

                        // Row for each exercise
                        var i = 0;
                        $.each(s.exercises, (exercise_index, exercise) => {
                            i++;

                            var tr = $('<div class="tableRow"><div class="tableCell" style="width: 1vw";><a class="toggleExerciseDetails">+</a></div><div class="tableCell minWidth"><a class="toggleExerciseDetails"><strong>Exercise ' + i + '</strong></a></div><div class="tableCell minWidth">(' + numHandinsExercises[exercise_index] + ' / ' + numStudents + ' handins)</div><div class="tableCell"><a class="loadExerciseSolution">Load suggested solution</a></div></div>');

                            tableGroup.append(tr);

                            // Click event handlers for load links
                            $(".loadExerciseSolution", tr).click(e => {
                                if (decodedExercises[exercise_index] === null) {
                                    customDialog("The proof code is invalid and could not be loaded.");
                                } else {
                                    customDialog("You will lose any unsaved work during load.", true, () => {
                                        loadProof(decodedExercises[exercise_index]);
                                        $(".closeCenteredOverlay", contentOuter).click();
                                    });
                                }
                            });

                            // Row for each student
                            $.each(s.students, (student_index, student) => {

                                var tr_student = $('<div class="tableRow student hidden" data-exercise-id="' + exercise_index + '"><div class="tableCell"></div><div class="tableCell minWidth">' + student + '</div><div class="tableCell minWidth">' + getFeedbackIcon(exercise_index, student_index) + '</div><div class="tableCell">'
                                    + (decodedHandins[exercise_index][student_index] !== undefined ? '<a class="loadStudentHandin">Load student handin</a>' : '-') + '</div></div>');

                                tableGroup.append(tr_student);

                                if (decodedHandins[exercise_index][student_index] !== undefined) {
                                    $(".loadStudentHandin", tr_student).click(e => {
                                        if (decodedHandins[exercise_index][student_index] === null) {
                                            customDialog("The proof code is invalid and could not be loaded.");
                                        } else {
                                            customDialog("You will lose any unsaved work during load.", true, () => {
                                                loadProof(decodedHandins[exercise_index][student_index]);
                                                $(".closeCenteredOverlay", contentOuter).click();
                                            });
                                        }
                                    });
                                }

                            });


                            $(".toggleExerciseDetails", tr).click(e => {
                                if ($(".toggleExerciseDetails:eq(0)", tr).html() == "+") {
                                    $(".tableRow[data-exercise-id=" + exercise_index + "]").removeClass("hidden");
                                    $(".toggleExerciseDetails:eq(0)", tr).html("-");
                                } else {
                                    $(".tableRow[data-exercise-id=" + exercise_index + "]").addClass("hidden");
                                    $(".toggleExerciseDetails:eq(0)", tr).html("+");
                                }
                            });
                        });

                        tableGroup.children(".tableRow").each((i, e) => {
                            $(e).mouseover(() => {
                                $(e).addClass("dark");
                            }).mouseleave(() => {
                                $(e).removeClass("dark");
                            });;
                        });

                        content.append(tableGroup);
                    } else {
                        handleCommonErrors(s.error);
                    }
                }
            });

            break;
        case UserType.ADMIN:
            //
            // Admin page
            //

            contentFlex.prepend(statusLine());

            var tableGroup = $('<div class="table bordered fullWidth"></div>');
            var tableInactiveUsers = $('<div class="table bordered fullWidth"></div>');

            function getAdminGroupTable() {
                tableGroup.children().remove();
                tableInactiveUsers.children().remove();

                // Table header
                tableGroup.append(
                    '<div class="tableRow">' +
                    '<div class="tableCell">Active</div>' +
                    '<div class="tableCell"></div>' +
                    '<div class="tableCell">Assignment</div>' +
                    '<div class="tableCell">&nbsp;</div>' +
                    '<div class="tableCell">&nbsp;</div>' +
                    '</div>');

                $.ajax({
                    url: "proofjudge.php",
                    type: "POST",
                    data: {
                        action: "get_admin_group_table"
                    },
                    dataType: "json",
                    error: function (err) {
                        console.log("Failed to read group data", err);
                    },
                    success: function (s) {
                        if (s.status === "success") {
                            $.each(s.assignments, (ia, a) => {
                                var tr = $('<div class="tableRow">' +
                                    '<div class="tableCell minWidth center"><input type="checkbox" name="active" /></div>' +
                                    '<div class="tableCell" style="width: 1vw";><a class="toggleAssignmentDetails">+</a></div>' +
                                    '<div class="tableCell"><a class="toggleAssignmentDetails"><strong>' + a.name + '</strong></a></div>' +
                                    '<div class="tableCell minWidth"><a class="editAssigmentBtn">Edit</a></div>' +
                                    '<div class="tableCell minWidth"><a class="deleteAssigmentBtn">x</a></div>' +
                                    '</div>');

                                tableGroup.append(tr);

                                $.each(s.exercises, (ig, g) => {
                                    if (ia !== ig)
                                        return true;

                                    var c = 0;
                                    $.each(g, (ie, e) => {
                                        s
                                        c++;

                                        var tr_s = $('<div class="tableRow hidden" data-assignment-id="' + ia + '">' +
                                            '<div class="tableCell minWidth"></div>' +
                                            '<div class="tableCell"></div>' +
                                            '<div class="tableCell" title="Goal: ' + e.solution + '">Exercise ' + c + '</div>' +
                                            '<div class="tableCell minWidth"></div>' +
                                            '<div class="tableCell minWidth"><a class="deleteExerciseBtn">x</a></div>' +
                                            '</div>');

                                        tableGroup.append(tr_s);

                                        $(".deleteExerciseBtn", tr_s).on("click", e => {
                                            customDialog("The exercise data cannot be recovered once deleted.\n\nDo you wish to continue?", true, () => {
                                                $.ajax({
                                                    url: "proofjudge.php",
                                                    type: "POST",
                                                    data: {
                                                        action: "delete_exercise",
                                                        exerciseID: ie
                                                    },
                                                    dataType: "json",
                                                    error: function (err) {
                                                        console.log("Failed to delete exercise from assignment.", err);
                                                    },
                                                    success: function (s) {
                                                        if (s.status === "success") {
                                                            getAdminGroupTable();
                                                            toggleEditMode();
                                                        } else {
                                                            handleCommonErrors(s.error);

                                                            switch (s.error) {
                                                                case 1:
                                                                    // Assigmnment still has students with handins
                                                                    customDialog("There are still handins for this exercise. Remove all handins to be able to delete the exercise.");
                                                                    break;
                                                            }
                                                        }
                                                    }
                                                });
                                            });
                                        });
                                    });
                                });

                                var student_ids = [];

                                $.each(s.students, (studentID, stud) => {
                                    if (stud.assignment_ids.some(aid => { return aid === ia; }))
                                        student_ids.push(studentID);
                                });

                                student_ids.forEach(studentID => {
                                    var tr_s = $('<div class="tableRow hidden" data-assignment-id="' + ia + '">' +
                                        '<div class="tableCell minWidth"></div>' +
                                        '<div class="tableCell minWidth"></div>' +
                                        '<div class="tableCell">' + s.students[studentID].username + '</div>' +
                                        '<div class="tableCell minWidth"></div>' +
                                        '<div class="tableCell minWidth"><a class="deleteStudentLinkBtn">x</a></div>' +
                                        '</div>');

                                    tableGroup.append(tr_s);

                                    $(".deleteStudentLinkBtn", tr_s).on("click", e => {
                                        customDialog("The student must be manually added again once removed.\n\nDo you wish to continue?", true, () => {
                                            $.ajax({
                                                url: "proofjudge.php",
                                                type: "POST",
                                                data: {
                                                    action: "delete_student_assignment_link",
                                                    assignmentID: ia,
                                                    userID: studentID
                                                },
                                                dataType: "json",
                                                error: function (err) {
                                                    console.log("Failed to remove student from assignment.", err);
                                                },
                                                success: function (s) {

                                                    if (s.status === "success") {
                                                        getAdminGroupTable();
                                                        toggleEditMode();
                                                    } else {
                                                        handleCommonErrors(s.error);

                                                        switch (s.error) {
                                                            case 1:
                                                                // Assigmnment still has students with handins
                                                                customDialog("The student's handin must be deleted in order to remove the student from the assignment.");
                                                                break;
                                                        }
                                                    }
                                                }
                                            });
                                        });
                                    });
                                });

                                $(".toggleAssignmentDetails", tr).click(e => {
                                    if ($(".toggleAssignmentDetails:eq(0)", tr).html() == "+") {
                                        $(".tableRow[data-assignment-id=" + ia + "]").removeClass("hidden");
                                        $(".toggleAssignmentDetails:eq(0)", tr).html("-");
                                    } else {
                                        $(".tableRow[data-assignment-id=" + ia + "]").addClass("hidden");
                                        $(".toggleAssignmentDetails:eq(0)", tr).html("+");
                                    }
                                });


                                $('input[name="active"]', tr).attr("checked", a.active);

                                $('input[name="active"]', tr).click(e => {
                                    var setChecked = $(e.currentTarget).attr("checked") != "checked";
                                    $(e.currentTarget).attr("checked", "false");

                                    $.ajax({
                                        url: "proofjudge.php",
                                        type: "POST",
                                        data: {
                                            action: "toggle_assignment_active",
                                            assignmentID: ia
                                        },
                                        dataType: "json",
                                        error: function (err) {
                                            console.log("Failed to toggle active flag on assignment.", err);
                                        },
                                        success: function (s) {
                                            if (setChecked) {
                                                $(e.currentTarget).attr("checked", "true");
                                            }
                                        }
                                    });
                                });

                                $(".deleteAssigmentBtn", tr).on("click", e => {
                                    $.ajax({
                                        url: "proofjudge.php",
                                        type: "POST",
                                        data: {
                                            action: "delete_assignment",
                                            assignmentID: ia
                                        },
                                        dataType: "json",
                                        error: function (err) {
                                            console.log("Failed to delete assignment.", err);
                                        },
                                        success: function (s) {
                                            if (s.status === "success") {
                                                getAdminGroupTable();
                                                toggleEditMode();
                                            } else {
                                                handleCommonErrors(s.error);

                                                switch (s.error) {
                                                    case 1:
                                                        // Assigmnment still has students with handins
                                                        customDialog("There are still exercises for this assignment. Delete all exercises before being able to remove the assignment.");
                                                        break;
                                                    case 2:
                                                        // Assigmnment still has students with handins
                                                        customDialog("There are still students in this assignment. Remove all students before being able to remove the assignment.");
                                                        break;
                                                }
                                            }
                                        }
                                    });
                                });

                                $(".editAssigmentBtn", tr).on("click", e => {
                                    toggleEditMode(true, ia, a.name);
                                });

                            });

                            tableGroup.children(".tableRow:not(:first)").add(tableInactiveUsers.children(".tableRow:not(:first)")).each((i, e) => {
                                $(e).mouseover(() => {
                                    $(e).addClass("dark");
                                }).mouseleave(() => {
                                    $(e).removeClass("dark");
                                });;
                            });

                            // See and delete "inactive" users
                            $.each(s.inactiveStudents, (i, studentID) => {
                                var tr_s = $('<div class="tableRow"><div class="tableCell">' + s.students[studentID].username + '</div><div class="tableCell"><a class="deleteStudentBtn">x</a></div></div>');

                                tableInactiveUsers.append(tr_s);

                                $(".deleteStudentBtn", tr_s).click(e => {
                                    customDialog("Once deleted the student data will be unrecoverable.\n\nDo you wish to continue?", true, () => {
                                        $.ajax({
                                            url: "proofjudge.php",
                                            type: "POST",
                                            data: {
                                                action: "delete_student_user",
                                                studentID: studentID
                                            },
                                            dataType: "json",
                                            error: function (err) {
                                                console.log("Failed to delete student.", err);
                                            },
                                            success: function (s) {
                                                if (s.status === "success") {
                                                    getAdminGroupTable();
                                                } else {
                                                    handleCommonErrors(s.error);

                                                    switch (s.error) {
                                                        case 1:
                                                            // Assigmnment still has students with handins
                                                            customDialog("Student is still linked to assignments.");
                                                            break;
                                                    }
                                                }
                                            }
                                        });
                                    });
                                });
                            });

                            if (s.inactiveStudents.length == 0) {
                                tableInactiveUsers.append('<div class="tableRow"><div class="tableCell"><i>No inactive student accounts.</i></div><div class="tableCell"></div></div>');
                            }

                        } else {
                            handleCommonErrors(s.error);
                        }
                    }
                });
            }

            getAdminGroupTable();

            var table = $('<div class="table fullWidth"></div>');
            var tableRow = $('<div class="tableRow"></div>');
            var leftColumn = $('<div class="tableCell halfOfTableWidth"></div>');
            var rightColumn = $('<div class="tableCell"></div>');

            content.append(table);
            table.append(tableRow);
            tableRow.append(leftColumn);
            tableRow.append('<div class="tableCell">&nbsp;</div>');
            tableRow.append(rightColumn);

            leftColumn.append(tableGroup);
            leftColumn.append('<div>&nbsp;</div>');
            leftColumn.append('<div class="textline">Inactive student accounts</div>');
            leftColumn.append(tableInactiveUsers);


            // Add/edit assignment

            var assignmentForm = $('<form id="assignmentForm"></form>');
            var assignmentTable = $('<div class="table fullWidth"></div>');
            assignmentTable.append('<div class="tableCaption textline dark"></div>');
            assignmentForm.append(assignmentTable);
            assignmentForm.append('<input type="hidden" name="assignmentID" value="0" />');
            assignmentTable.append('<div class="tableRow"><div class="tableCell">Assignment name</div><div class="tableCell minWidth"><input type="text" class="proofJudgeInputText" name="assignmentName" /></div></div>');
            assignmentTable.append('<div class="tableRow"><div class="tableCell">Assistant password</div><div class="tableCell minWidth"><input type="password" class="proofJudgeInputText" name="assistantPassword" /></div></div>');
            assignmentTable.append('<div class="tableRow"><div class="tableCell">Students</div><div class="tableCell minWidth"><textarea rows="15" cols="65" class="proofJudgeInputText" name="students"></textarea></div></div>');
            assignmentTable.append('<div class="tableRow"><div class="tableCell"></div><div class="tableCell"><input type="button" name="check_newness_students" value="Check newness students" /></div></div>');
            assignmentTable.append('<div class="tableRow"><div class="tableCell">Exercises</div><div class="tableCell minWidth"><textarea rows="15" cols="65" class="proofJudgeInputText" name="exercises"></textarea></div></div>');
            assignmentTable.append('<div class="tableRow"><div class="tableCell"></div><div class="tableCell"><div id="divButtons"><input type="submit" name="add" /></div></div></div>');

            rightColumn.append(assignmentForm);

            $('input[name="check_newness_students"]', assignmentForm).click(e => {

                $.ajax({
                    url: "proofjudge.php",
                    type: "POST",
                    data: {
                        action: "check_newness_students",
                        students: $('textarea[name="students"]').val()
                    },
                    dataType: "json",
                    error: function (err) {
                        console.log("Failed check newness of students.", err);
                    },
                    success: function (s) {
                        var arrStudents: String[] = $.map(s.studentsExisting, (v, k) => { return v; })

                        if (s.status === "success") {
                            if (arrStudents.length > 0) {
                                customDialog("Found student accounts for:\n" + arrStudents.join("\n"));
                            } else {
                                customDialog("Found no existing student accounts.");
                            }
                        } else {
                            handleCommonErrors(s.error);
                        }
                    }
                });
            });

            $(assignmentForm).on("submit", e => {
                var ok = true;
                if ($('textarea[name="exercises"]').val().length > 0) {
                    var exerciseString: string = $('textarea[name="exercises"]').val();

                    var exerciseStringLines = exerciseString.split(/[\r\n]+/);

                    exerciseStringLines.forEach((line, i) => {
                        if (!isValidProofCode(line)) {
                            customDialog("Invalid proof code:\nExercise " + (i + 1) + " (" + line.substr(0, 10) + (line.length > 10 ? "..." : "") + ")");
                            ok = false;
                        }
                    });
                }

                if (!ok) {
                    return false;
                }

                $.ajax({
                    url: "proofjudge.php",
                    type: "POST",
                    data: {
                        action: "submit_admin_assignment_data",
                        assignmentID: $('input[name="assignmentID"]').val(),
                        assignmentName: $('input[name="assignmentName"]').val(),
                        assistantPassword: $('input[name="assistantPassword"]').val(),
                        students: $('textarea[name="students"]').val(),
                        exercises: $('textarea[name="exercises"]').val()
                    },
                    dataType: "json",
                    error: function (err) {
                        console.log("Failed to submit group data", err);
                    },
                    success: function (s) {
                        if (s.status === "success") {
                            getAdminGroupTable();
                            toggleEditMode();
                        } else {
                            handleCommonErrors(s.error);

                            switch (s.error) {
                                case 1:
                                    customDialog("Invalid assignment name. Please use only characters A-z, 0-9 and spaces.");
                                    break;
                                case 2:
                                    customDialog("Invalid assistant password. Please use only characters A-z and 0-9 with no spaces.");
                                    break;
                                case 3:
                                    customDialog("Invalid student data passed. Please seperate username and password by a space. Seperate multiple student accounts by line breaks.");
                                    break;
                                case 4:
                                    customDialog("Invalid student name(s). Please use only characters A-z and 0-9 with no spaces.");
                                    break;
                                case 5:
                                    customDialog("Invalid student password(s). Please use only characters A-z and 0-9 with no spaces.");
                                    break;
                                case 6:
                                    customDialog("Invalid exercise(s). Please use only valid NaDeA load code.");
                                    break;
                                case 7:
                                    customDialog("Could not find assignment to be updated.");
                                    break;
                                case 8:
                                    customDialog("Assignment name is not available. Please choose a different name.");
                                    break;
                            }
                        }
                    }
                });

                return false;
            });

            function toggleEditMode(edit: boolean = false, assignmentID: number = null, assignmentName: string = null) {
                $('#divButtons').children('input[name="cancel"]').remove();

                if (edit && assignmentID > 0) {
                    //
                    // Edit assignment
                    //

                    $(".tableCaption", assignmentForm).html("Edit assignment: <strong>" + assignmentName + "</strong>");

                    $('input[name="assignmentID"]').val(assignmentID.toString());
                    $('input[name="assignmentName"]').val(assignmentName);
                    $('input[name="assistantPassword"]').val("");
                    $('textarea[name="students"]').val("");
                    $('textarea[name="exercises"]').val("");

                    var cancel = $('<input type="button" class="marginRight" name="cancel" value="Cancel" />');

                    $('#divButtons').prepend(cancel);
                    $(':submit', assignmentForm).attr("value", "Update assignment");

                    cancel.on("click", e => {
                        toggleEditMode();
                    });

                } else {
                    //
                    // Create new assignment
                    //

                    $(".tableCaption", assignmentForm).html("New assignment");

                    $('input[name="assignmentID"]').val("0");
                    $('input[name="assignmentName"]').val("");
                    $('input[name="assistantPassword"]').val("");
                    $('textarea[name="students"]').val("");
                    $('textarea[name="exercises"]').val("");

                    $(':submit', assignmentForm).attr("value", "Add new assignment");
                }
            }

            toggleEditMode();

            break;
        default:
            console.log(loggedInUser);
            throw new Error("Invalid user type");
    }

    contentOuter.prepend("<div class=\"closeCenteredOverlay\"><div>X</div></div>");
    contentOuter.show();

    $(".closeCenteredOverlay", contentOuter).click(function (e) {
        $(outer).remove();
        setTitle();
    });
}
