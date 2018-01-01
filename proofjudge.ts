/// <reference path="references.d.ts" />

// Enumeration of user types including offline status/
enum UserType {
    OFFLINE = 0,
    STUDENT = 1,
    TEACHER = 2,
    ASSISTANT = 3,
    ADMIN = 4
}

interface UserSessionData { name?: string, courseName?: string, accessRights: UserType };

// Global user variable
var loggedInUser: UserSessionData = {
    accessRights: UserType.OFFLINE
};

function updateLoginData(user: UserSessionData) {
    loggedInUser = user;

    if (user.accessRights == UserType.OFFLINE) {
        $(".proofjudgeBtn").html("ProofJudge");
    } else {
        $(".proofjudgeBtn").html("Logged in...");
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
        console.log("Failed to get login data", err);
        updateLoginData({ accessRights: UserType.OFFLINE });
    },
    success: function (s) {
        if (s.status === "success") {
            var forceReload = loggedInUser.accessRights != s.accessRights;

            updateLoginData({ name: s.username, accessRights: s.accessRights, courseName: s.courseName });

            if (forceReload && $(".overlay.proofjudge").length > 0) {
                $(".closeCenteredOverlay").click();
                proofJudgeOverlay();
            }
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

    tr.append('<div class="tableCell">Logged in as <strong>' + loggedInUser.name + '</strong> (' + (loggedInUser.accessRights == UserType.ADMIN ? "admin" : loggedInUser.courseName) + ')</div>');

    var logoutTd = $('<div class="tableCell"></div>');
    var logoutLink = $('<a class="logoutBtn">Logout</a>');

    logoutTd.append(logoutLink);
    tr.append(logoutTd);
    sl.append(tr);

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
    $.ajax(ajaxSettings);

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

            content.append('<form id="loginArea"><div class="table"><div class="tableRow"><div class="tableCell">Username:</div><div class="tableCell"><input type="text" class="proofJudgeInputText" name="username" /></div></div><div class="tableRow"><div class="tableCell">Password:</div><div class="tableCell"><input type="password" class="proofJudgeInputText" name="password" /></div></div><div class="tableRow"><div class="tableCell">Course:</div><div class="tableCell"><select name="group" id="groupSelector"><option value="0"></option></select></div></div><div class="tableRow"><div class="tableCell"></div><div class="tableCell"><div class="floatRight"><input type="button" value="Cancel" />&nbsp;<input type="submit" value="Login" /></div></div></div></div></form>');

            $.ajax({
                url: "proofjudge.php",
                type: "POST",
                data: {
                    action: "get_group_data"
                },
                dataType: "json",
                error: function (err) {
                    console.log("Failed to get group data", err);
                },
                success: function (s) {
                    if (s.status === "success") {
                        var groups = [];

                        $.each(s.groups, (group_id, group) => { groups.push({ id: group_id, val: group }); });

                        groups.sort((l, r) => l.val.localeCompare(r.val)).forEach(x => {
                            $("#groupSelector").append('<option value="' + x.id + '">' + x.val + '</option>');
                        });
                    } else {
                        handleCommonErrors(s.error);
                    }

                }
            });

            // Login through ajax
            $("#loginArea").on("submit", e => {
                $.ajax({
                    url: "proofjudge.php",
                    type: "POST",
                    data: {
                        action: "authenticate_login",
                        username: $("#loginArea input[name='username']").val(),
                        password: $("#loginArea input[name='password']").val(),
                        courseID: $("#loginArea select[name='group']").val()
                    },
                    dataType: "json",
                    error: function (err) {
                        console.log("Failed to authenticate login", err);
                        updateLoginData({ accessRights: UserType.OFFLINE });
                    },
                    success: function (s) {
                        if (s.status === "success") {
                            updateLoginData({ name: s.username, accessRights: s.accessRights, courseName: s.courseName });

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
            var leftColumn = $('<div class="tableCell" style="width: 80%;"></div>');
            var rightColumn = $('<div class="tableCell"></div>');

            table.append(tableRow);
            tableRow.append(leftColumn);
            tableRow.append('<div class="tableCell">&nbsp;</div>');
            tableRow.append(rightColumn);
            content.append(table);

            var draftProofIDs = [];
            var draftProofs = [];

            // List of assignments
            var assignmentTable = $('<div class="table fullWidth bordered"></div>');

            function dropdownDraftSelector(exerciseID: number, proofCode: String, selectedDraftID: number = null, openForHandin: boolean): JQuery {
                var dropdown = $('<select id="selectSolution_' + exerciseID + '"' + (openForHandin ? "" : "disabled='disabled'") + '></select>');
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
                                //
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
                                    case 2:
                                        // Exercise not found, or assignment is inactive
                                        customDialog("The assignment is no longer open for handins.");
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
                                assignmentTable.append('<div class="tableRow dark"><div class="tableCell minWidth"><strong>' + a.name + '</strong></div><div class="tableCell">Goal</div><div class="tableCell minWidth">Selected solution</div></div>');

                                var eCount = 0;
                                $.each(a.exercises, (e_id, e) => {
                                    eCount++;

                                    var tr = $('<div class="tableRow"></div>')

                                    var proofObject = decodeProof(e.goal);

                                    tr.append('<div class="tableCell minWidt alignMiddle">Exercise ' + eCount + '</div><div class="tableCell smallFont alignMiddle formalSyntax">' + (proofObject ? getFormalSyntax(proofObject[0].goal, 0, null, [proofObject[0].goal]) : "-") + '</div><div class="tableCell minWidth alignMiddle"></div>');
                                    $("div.tableCell:eq(2)", tr).append(dropdownDraftSelector(e_id, e.goal, e.handin_draft_id, a.openForHandin));

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

            var draftTable = $('<div class="table fullWidth bordered"></div>');

            function getDraftTable() {
                draftTable.children().remove();

                // Current drafts
                draftTable.append('<div class="tableRow dark"><div class="tableCell minWidth">Draft</div><div class="tableCell">Goal</div><div class="tableCell minWidth">Number of ¤</div><div class="tableCell minWidth">Proof rules used</div><div class="tableCell minWidth"></div><div class="tableCell minWidth"></div></div>');

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

                                var tr = $('<div class="tableRow"><div class="tableCell alignMiddle">' + d.name + '</div><div class="tableCell formalSyntax alignMiddle smallFont">' + (draftProofs[d_id].proofObject ? getFormalSyntax(draftProofs[d_id].proofObject[0].goal, 0, null, [draftProofs[d_id].proofObject[0].goal]) : "-") + '</div><div class="tableCell alignRight alignMiddle">' + (draftProofs[d_id].proofObject ? countUnknowns(draftProofs[d_id].proofObject[0]) : "-") + '</div><div class="tableCell alignRight alignMiddle">' + (draftProofs[d_id].proofObject ? countNoProofRules(draftProofs[d_id].proofObject[0]) : "-") + '</div><div class="tableCell minWidth loadDraft alignMiddle"><a>Load draft</a></div><div class="tableCell deleteDraft"></div></div>');

                                draftTable.append(tr);

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
            var saveDraftTable = $('<div class="table fullWidth"></div>');
            saveDraftForm.append(saveDraftTable);

            saveDraftTable.append('<div class="tableCaption textline dark"><strong>Create draft of current proof state:</strong></div>');
            saveDraftTable.append('<div class="tableRow"><div class="tableCell minWidth">Draft name</div><div class="tableCell"><input type="text" class="proofJudgeInputText" name="draftName" maxlength="64" /></div></div');

            var draftGoalDiv = $('<div class="tableRow"><div class="tableCell minWidth">Goal:</div><div class="tableCell alignRight">' + getFormalSyntax(currentState.p.goal, 0, null, [...currentState.p.assumptions, currentState.p.goal]) + '</div></div');

            saveDraftTable.append(draftGoalDiv);
            saveDraftTable.append('<div class="tableRow"><div class="tableCell minWidth">Number of <span class="formalUnknown">¤</span>:</div><div class="tableCell alignRight">' + countUnknowns(currentState.p) + ' </div></div');
            saveDraftTable.append('<div class="tableRow"><div class="tableCell minWidth">Proof rules used:</div><div class="tableCell alignRight">' + countNoProofRules(currentState.p) + '</div></div');
            saveDraftTable.append('<div class="tableRow"><div class="tableCell minWidth"></div><div class="tableCell alignRight"><input type="submit" value="Save draft" style="text-align: center;" /></div></div');

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
                            });
                        });

                        content.append(tableGroup);
                    } else {
                        handleCommonErrors(s.error);
                    }
                }
            });

            break;
        case UserType.TEACHER:
            //
            // Teacher page
            //

            contentFlex.prepend(statusLine());

            var tableGroup = $('<div class="table bordered fullWidth"></div>');
            var tableInactiveUsers = $('<div class="table bordered fullWidth"></div>');

            function getTeacherGroupTable(open: number = null) {
                tableGroup.children().remove();
                tableInactiveUsers.children().remove();

                // Table header
                $.ajax({
                    url: "proofjudge.php",
                    type: "POST",
                    data: {
                        action: "get_teacher_course_table"
                    },
                    dataType: "json",
                    error: function (err) {
                        console.log("Failed to read group data", err);
                    },
                    success: function (s) {
                        if (s.status === "success") {

                            if (s.assignments.length == 0) {
                                var tr = $('<div class="tableCaption textline" style="padding: 0;"><em>There are no assignments for this course.</em></div>');
                                tableGroup.append(tr);
                            }

                            $.each(s.assignments, (ia, a) => {
                                var tr = $('<div class="tableRow">' +
                                    '<div class="tableCell" style="width:1.5vw; text-align: center;"><a class="toggleAssignmentDetails">+</a></div>' +
                                    '<div class="tableCell minWidth"><a class="toggleAssignmentDetails"><strong>' + a.name + '</strong></a></div>' +
                                    '<div class="tableCell"></div>' +
                                    '<div class="tableCell minWidth center">Active <input type="checkbox" name="active" /></div>' +
                                    '<div class="tableCell minWidth center">Open for handin <input type="checkbox" name="open_for_handin" /></div>' +
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

                                        var exerciseProofObject = decodeProof(e.solution);

                                        var tr_s = $('<div class="tableRow hidden" data-assignment-id="' + ia + '">' +
                                            '<div class="tableCell" style="width:1.5vw;"></div>' +
                                            '<div class="tableCell minWidth">Exercise ' + c + '</div>' +
                                            '<div class="tableCell">' + (exerciseProofObject ? getFormalSyntax(exerciseProofObject[0].goal, 0, null, [exerciseProofObject[0].goal]) : "-") + '</div>' +
                                            '<div class="tableCell minWidth"></div>' +
                                            '<div class="tableCell minWidth"></div>' +
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
                                                            getTeacherGroupTable(ia);
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

                                var studentIDs = [];
                                var assistantIDs = [];

                                $.each(s.users.students, (userID, user) => {
                                    if (user.assignmentIDs.some(aid => { return aid === ia; }))
                                        studentIDs.push(userID);
                                });

                                $.each(s.users.assistants, (userID, user) => {
                                    if (user.assignmentIDs.some(aid => { return aid === ia; }))
                                        assistantIDs.push(userID);
                                });

                                function createUserRow(userID, isStudent: boolean) {
                                    var tr_s = $('<div class="tableRow hidden" data-assignment-id="' + ia + '">' +
                                        '<div class="tableCell" style="width:1.5vw;"></div>' +
                                        '<div class="tableCell minWidth">' + (isStudent ? "Student" : "Assistant") + " " + (isStudent ? s.users.students : s.users.assistants)[userID].username + '</div>' +
                                        '<div class="tableCell"><a class="resetPasswords">Reset passwords</a></div>' +
                                        '<div class="tableCell minWidth"></div>' +
                                        '<div class="tableCell minWidth"></div>' +
                                        '<div class="tableCell minWidth"></div>' +
                                        '<div class="tableCell minWidth"><a class="deleteUserLinkBtn">x</a></div>' +
                                        '</div>');

                                    tableGroup.append(tr_s);

                                    $(".deleteUserLinkBtn", tr_s).on("click", e => {
                                        customDialog("The student must be manually added again once removed.\n\nDo you wish to continue?", true, () => {
                                            $.ajax({
                                                url: "proofjudge.php",
                                                type: "POST",
                                                data: {
                                                    action: "delete_user_assignment_link",
                                                    assignmentID: ia,
                                                    userID: userID
                                                },
                                                dataType: "json",
                                                error: function (err) {
                                                    console.log("Failed to remove student/assistant from assignment.", err);
                                                },
                                                success: function (s) {

                                                    if (s.status === "success") {
                                                        getTeacherGroupTable(ia);
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

                                    $(".resetPasswords", tr_s).on("click", e => {
                                        customDialog("You are about to reset all passwords for this " + (isStudent ? "student" : "assistant") + ".\n\nDo you wish to continue?", true, () => {
                                            $.ajax({
                                                url: "proofjudge.php",
                                                type: "POST",
                                                data: {
                                                    action: "reset_passwords",
                                                    userID: userID
                                                },
                                                dataType: "json",
                                                error: function (err) {
                                                    console.log("Failed to reset passwords for " + (isStudent ? "student" : "assistant") + ".", err);
                                                },
                                                success: function (s) {
                                                    if (s.status === "success") {
                                                        //
                                                    } else {
                                                        handleCommonErrors(s.error);

                                                        switch (s.error) {
                                                            case 1:
                                                            case 2:
                                                                // Assigmnment still has students with handins
                                                                customDialog("The " + (isStudent ? "student" : "assistant") + " account could not be found, or is not linked to this course.");
                                                                break;
                                                        }
                                                    }
                                                }
                                            });
                                        });
                                    });
                                }

                                studentIDs.forEach(userID => {
                                    createUserRow(userID, true);
                                });

                                assistantIDs.forEach(userID => {
                                    createUserRow(userID, false);
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
                                $('input[name="open_for_handin"]', tr).attr("checked", a.openForHandin);

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

                                $('input[name="open_for_handin"]', tr).click(e => {
                                    var setChecked = $(e.currentTarget).attr("checked") != "checked";
                                    $(e.currentTarget).attr("checked", "false");

                                    $.ajax({
                                        url: "proofjudge.php",
                                        type: "POST",
                                        data: {
                                            action: "toggle_assignment_open_for_handin",
                                            assignmentID: ia
                                        },
                                        dataType: "json",
                                        error: function (err) {
                                            console.log("Failed to toggle open for handin flag on assignment.", err);
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
                                                getTeacherGroupTable(ia);
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

                                if (open) {
                                    $(".tableRow[data-assignment-id=" + open + "]").parent().children(".tableRow:first").children(":first").children().click();
                                }
                            });

                            tableGroup.children(".tableRow:not(:first)").add(tableInactiveUsers.children(".tableRow:not(:first)")).each((i, e) => {
                                $(e).mouseover(() => {
                                    $(e).addClass("dark");
                                }).mouseleave(() => {
                                    $(e).removeClass("dark");
                                });
                            });

                            // See and delete "inactive" 
                            $.each(s.inactiveUsers, (i, user) => {
                                var tr_s = $('<div class="tableRow"><div class="tableCell">' + user.username + '</div><div class="tableCell minWidth"><a class="deleteUserBtn">x</a></div></div>');

                                tableInactiveUsers.append(tr_s);

                                $(".deleteUserBtn", tr_s).click(e => {
                                    customDialog("Once deleted the user data will be unrecoverable.\n\nDo you wish to continue?", true, () => {
                                        $.ajax({
                                            url: "proofjudge.php",
                                            type: "POST",
                                            data: {
                                                action: "delete_user",
                                                userID: user.id
                                            },
                                            dataType: "json",
                                            error: function (err) {
                                                console.log("Failed to delete student/assistant.", err);
                                            },
                                            success: function (s) {
                                                if (s.status === "success") {
                                                    getTeacherGroupTable(open);
                                                } else {
                                                    handleCommonErrors(s.error);

                                                    switch (s.error) {
                                                        case 1:
                                                            // Assigmnment still has students with handins
                                                            customDialog("Student/assistant is still linked to assignments.");
                                                            break;
                                                        case 2:
                                                            // User not from this course
                                                            customDialog("Could not find student/assistant in this course.");
                                                            break;
                                                    }
                                                }
                                            }
                                        });
                                    });
                                });
                            });

                            if (s.inactiveUsers.length == 0) {
                                tableInactiveUsers.append('<div class="tableRow"><div class="tableCell"><i>No inactive student or assistant accounts.</i></div><div class="tableCell"></div></div>');
                            }

                        } else {
                            handleCommonErrors(s.error);
                        }
                    }
                });
            }

            getTeacherGroupTable();

            var table = $('<div class="table fullWidth"></div>');
            var tableRow = $('<div class="tableRow"></div>');
            var leftColumn = $('<div class="tableCell" style="width: 60%;"></div>');
            var rightColumn = $('<div class="tableCell"></div>');

            content.append(table);
            table.append(tableRow);
            tableRow.append(leftColumn);
            tableRow.append('<div class="tableCell">&nbsp;</div>');
            tableRow.append(rightColumn);

            leftColumn.append(tableGroup);
            leftColumn.append('<div>&nbsp;</div>');
            leftColumn.append('<div class="textline">Inactive student and/or assistant accounts</div>');
            leftColumn.append(tableInactiveUsers);


            // Add/edit assignment

            var assignmentForm = $('<form id="assignmentForm"></form>');
            var assignmentTable = $('<div class="table fullWidth"></div>');
            assignmentTable.append('<div class="tableCaption textline dark"></div>');
            assignmentForm.append(assignmentTable);
            assignmentForm.append('<input type="hidden" name="assignmentID" value="0" />');
            assignmentTable.append('<div class="tableRow"><div class="tableCell">Assignment name</div><div class="tableCell minWidth"><input type="text" class="proofJudgeInputText" name="assignmentName" /></div></div>');
            assignmentTable.append('<div class="tableRow"><div class="tableCell">Exercises</div><div class="tableCell minWidth"><textarea rows="10" cols="50" class="proofJudgeInputText" name="exercises"></textarea></div></div>');
            assignmentTable.append('<div class="tableRow"><div class="tableCell">Students</div><div class="tableCell minWidth"><textarea rows="10" cols="50" class="proofJudgeInputText" name="students"></textarea></div></div>');
            assignmentTable.append('<div class="tableRow"><div class="tableCell">Assistants</div><div class="tableCell minWidth"><textarea rows="5" cols="50" class="proofJudgeInputText" name="assistants"></textarea></div></div>');
            assignmentTable.append('<div class="tableRow"><div class="tableCell"></div><div class="tableCell"><div id="divButtons"><input type="submit" name="add" class="marginRight" /><input type="button" name="check_newness_students" value="Check newness of usernames" /></div></div></div>');

            rightColumn.append(assignmentForm);

            $('input[name="check_newness_students"]', assignmentForm).click(e => {
                $.ajax({
                    url: "proofjudge.php",
                    type: "POST",
                    data: {
                        action: "check_newness_usernames",
                        users: $('textarea[name="students"]').val() + "\n" + $('textarea[name="assistants"]').val()
                    },
                    dataType: "json",
                    error: function (err) {
                        console.log("Failed to check newness of usernames.", err);
                    },
                    success: function (s) {
                        var usersExisting: String[] = $.map(s.usersExisting, (v, k) => { return v; })

                        if (s.status === "success") {
                            if (usersExisting.length > 0) {
                                customDialog("Found existing students/assistants for usernames:\n" + usersExisting.join("\n"));
                            } else {
                                customDialog("Found no existing students/assistants.");
                            }
                        } else {
                            handleCommonErrors(s.error);

                            switch (s.error) {
                                case 1:
                                    customDialog("Invalid format.");
                                    break;
                                case 2:
                                    customDialog("Found username " + s.username + "multiple times as student and/or assistant.");
                                    break;
                            }
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
                        action: "submit_assignment_data",
                        assignmentID: $('input[name="assignmentID"]').val(),
                        assignmentName: $('input[name="assignmentName"]').val(),
                        students: $('textarea[name="students"]').val(),
                        assistants: $('textarea[name="assistants"]').val(),
                        exercises: $('textarea[name="exercises"]').val()
                    },
                    dataType: "json",
                    error: function (err) {
                        console.log("Failed to submit group data", err);
                    },
                    success: function (s) {
                        if (s.status === "success") {
                            getTeacherGroupTable();
                            toggleEditMode(true, $('input[name="assignmentID"]').val(), $('input[name="assignmentName"]').val());
                        } else {
                            handleCommonErrors(s.error);

                            switch (s.error) {
                                case 1:
                                    customDialog("Invalid assignment name. Please use only characters A-z, 0-9 and spaces.");
                                    break;
                                case 2:
                                    customDialog("Invalid student data passed. Please seperate username and password by a space. Seperate multiple student accounts by line breaks.");
                                    break;
                                case 3:
                                    customDialog("Invalid username(s). Please use only characters A-z and 0-9 with no spaces.");
                                    break;
                                case 4:
                                    customDialog("Invalid password(s). Please use only characters A-z and 0-9 with no spaces.");
                                    break;
                                case 5:
                                    customDialog("Invalid exercise(s). Please use only valid NaDeA load code.");
                                    break;
                                case 6:
                                    customDialog("Could not find assignment to be updated.");
                                    break;
                                case 7:
                                    customDialog("Assignment name is not available. Please choose a different name.");
                                    break;
                                case 8:
                                    customDialog("Assignment is not from this course.");
                                    break;
                                case 9:
                                case 10:
                                    customDialog("Username " + s.username + " is not available.");
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
                    $('textarea[name="assistants"]').val("");
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
                    $('textarea[name="assistants"]').val("");
                    $('textarea[name="exercises"]').val("");

                    $(':submit', assignmentForm).attr("value", "Add new assignment");
                }
            }

            toggleEditMode();

            break;
        case UserType.ADMIN:
            //
            // Admin page
            //

            contentFlex.prepend(statusLine());

            var table = $('<div class="table fullWidth"></div>');
            var tableRow = $('<div class="tableRow"></div>');
            var leftColumn = $('<div class="tableCell" style="width: 70%";></div>');
            var rightColumn = $('<div class="tableCell"></div>');

            table.append(tableRow);
            tableRow.append(leftColumn);
            tableRow.append('<div class="tableCell">&nbsp;</div>');
            tableRow.append(rightColumn);
            content.append(table);

            // List of assignments
            var courseTable = $('<div class="table bordered fullWidth"></div>');
            courseTable.append('<div class="tableRow dark"><div class="tableCell minWidth">Course</div><div class="tableCell minWidth">Teacher</div><div class="tableCell"></div><div class="tableCell minWidth">Students</div><div class="tableCell minWidth">Assistants</div><div class="tableCell minWidth">Assignments</div><div class="tableCell minWidth">&nbsp;&nbsp;</div></div>');

            var inactiveTeachersTable = $('<div class="table bordered fullWidth"></div>');

            function recreateCourseTable() {
                $(".tableRow", courseTable).not(":first").remove();
                $(".tableRow", inactiveTeachersTable).remove();

                $.ajax({
                    url: "proofjudge.php",
                    type: "POST",
                    data: {
                        action: "get_course_table"
                    },
                    dataType: "json",
                    contentType: "application/x-www-form-urlencoded; charset:ISO-8859-1",
                    error: function (err) {
                        console.log("Failed to get course data", err);
                    },
                    success: function (s) {
                        if (s.status === "success") {
                            $.each(s.courses, (i, courseRow) => {
                                var courseID = courseRow.courseID;

                                var tr = $('<div class="tableRow"></div>');

                                tr.append('<div class="tableCell minWidth">' + courseRow.name + '</div>');
                                tr.append('<div class="tableCell minWidth">' + courseRow.teacherName + '</div>');
                                tr.append('<div class="tableCell"><a class="resetPasswords">Reset teacher passwords</a></div>');
                                tr.append('<div class="tableCell center">' + courseRow.numStudents + '</div>');
                                tr.append('<div class="tableCell center">' + courseRow.numAssistants + '</div>');
                                tr.append('<div class="tableCell center">' + courseRow.numAssignments + '</div>');
                                tr.append('<div class="tableCell"><div class="deleteCourse"></div></div>');

                                if (courseRow.numStudents > 0 || courseRow.numAssistants > 0 || courseRow.numAssignments > 0) {
                                    $(".deleteCourse", tr).html("-").attr("title", "Only empty courses can be deleted.");
                                } else {
                                    $(".deleteCourse", tr).html("<a>x</a>").click(e => {
                                        customDialog("The course cannot be recovered once deleted.\n\nDo you wish to continue?", true, () => {
                                            $.ajax({
                                                url: "proofjudge.php",
                                                type: "POST",
                                                data: {
                                                    action: "delete_course",
                                                    courseID: courseID
                                                },
                                                dataType: "json",
                                                error: function (err) {
                                                    console.log("Failed to delete course.", err);
                                                },
                                                success: function (s) {
                                                    if (s.status === "success") {
                                                        recreateCourseTable();
                                                    } else {
                                                        handleCommonErrors(s.error);

                                                        console.log(s);

                                                        switch (s.error) {
                                                            case 1:
                                                                customDialog("Course (" + courseRow.name + ") could not be found.");
                                                                break;
                                                            case 2:
                                                                customDialog("Course (" + courseRow.name + ") still has students, assistants or assignments and cannot be deleted.");
                                                                break;
                                                        }
                                                    }
                                                }
                                            });
                                        });
                                    });
                                }

                                $(".resetPasswords", tr).on("click", e => {
                                    customDialog("You are about to reset all passwords for this teacher.\n\nDo you wish to continue?", true, () => {
                                        $.ajax({
                                            url: "proofjudge.php",
                                            type: "POST",
                                            data: {
                                                action: "reset_passwords",
                                                userID: courseRow.teacherID
                                            },
                                            dataType: "json",
                                            error: function (err) {
                                                console.log("Failed to reset passwords for teacher.", err);
                                            },
                                            success: function (s) {
                                                if (s.status === "success") {
                                                    //
                                                } else {
                                                    handleCommonErrors(s.error);

                                                    switch (s.error) {
                                                        case 1:
                                                        case 2:
                                                            // Assigmnment still has students with handins
                                                            customDialog("The teacher account could not be found, or is not linked to this course.");
                                                            break;
                                                    }
                                                }
                                            }
                                        });
                                    });
                                });

                                courseTable.append(tr);
                            });

                        } else {
                            handleCommonErrors(s.error);
                        }
                    }

                });

                $.ajax({
                    url: "proofjudge.php",
                    type: "POST",
                    data: {
                        action: "get_inactive_teachers"
                    },
                    dataType: "json",
                    contentType: "application/x-www-form-urlencoded; charset:ISO-8859-1",
                    error: function (err) {
                        console.log("Failed to get data for inactive teachers", err);
                    },
                    success: function (s) {
                        if (s.status === "success") {
                            $.each(s.inactiveTeachers, (userID, username) => {
                                var tr = $('<div class="tableRow"><div class="tableCell">' + username + '</div><div class="tableCell minWidth"><a class="deleteTeacher">x</a></div></div>');

                                inactiveTeachersTable.append(tr);

                                $(".deleteTeacher", tr).click(e => {
                                    customDialog("The teacher cannot be recovered once deleted.\n\nDo you wish to continue?", true, () => {
                                        $.ajax({
                                            url: "proofjudge.php",
                                            type: "POST",
                                            data: {
                                                action: "delete_teacher",
                                                userID: userID
                                            },
                                            dataType: "json",
                                            error: function (err) {
                                                console.log("Failed to delete teacher.", err);
                                            },
                                            success: function (s) {
                                                if (s.status === "success") {
                                                    recreateCourseTable();
                                                } else {
                                                    handleCommonErrors(s.error);

                                                    console.log(s);

                                                    switch (s.error) {
                                                        case 1:
                                                            customDialog("Teacher is not inactive and cannot be deleted.");
                                                            break;
                                                    }
                                                }
                                            }
                                        });
                                    });
                                });
                            });

                            if (s.inactiveTeachers.length == 0) {
                                inactiveTeachersTable.append('<div class="tableRow"><div class="tableCell"><i>No inactive teacher accounts.</i></div><div class="tableCell"></div></div>');
                            }

                        } else {
                            handleCommonErrors(s.error);
                        }
                    }

                });

                courseTable.children(".tableRow:not(:first)").add(inactiveTeachersTable.children(".tableRow:not(:first)")).each((i, e) => {
                    $(e).mouseover(() => {
                        $(e).addClass("dark");
                    }).mouseleave(() => {
                        $(e).removeClass("dark");
                    });
                });
            }

            recreateCourseTable();

            leftColumn.append(courseTable);
            leftColumn.append('<div>&nbsp;</div>');
            leftColumn.append('<div class="textline">Inactive teacher accounts</div>');
            leftColumn.append(inactiveTeachersTable);

            var courseCreationForm = $('<form id="createCourseForm"></form>');
            var formTable = $('<div class="table"></div>');
            courseCreationForm.append(formTable);

            formTable.append('<div class="tableCaption textline dark"><strong>Create new course</strong></div>');
            formTable.append('<div class="tableRow"><div class="tableCell">Course name</div><div class="tableCell"><input type="text" class="proofJudgeInputText" name="courseName" maxlength="64" /></div></div');
            formTable.append('<div class="tableRow"><div class="tableCell">Teacher username</div><div class="tableCell"><input type="text" class="proofJudgeInputText" name="teacherUsername" maxlength="64" /></div></div');
            formTable.append('<div class="tableRow"><div class="tableCell">Teacher password</div><div class="tableCell"><input type="password" class="proofJudgeInputText" name="teacherPassword" maxlength="64" /></div></div');

            formTable.append('<div class="tableRow"><div class="tableCell"></div><div class="tableCell"><div id="divButtons"><input type="submit" name="add" value="Save" /></div></div></div>');

            $(courseCreationForm).on("submit", e => {
                $.ajax({
                    url: "proofjudge.php",
                    type: "POST",
                    data: {
                        action: "submit_course",
                        courseName: $('input[name="courseName"]').val(),
                        teacherUsername: $('input[name="teacherUsername"]').val(),
                        teacherPassword: $('input[name="teacherPassword"]').val()
                    },
                    dataType: "json",
                    error: function (err) {
                        console.log("Failed to submit course", err);
                    },
                    success: function (s) {
                        if (s.status === "success") {

                            recreateCourseTable();

                        } else {
                            handleCommonErrors(s.error);

                            switch (s.error) {
                                case 1:
                                    customDialog("Invalid course name", false);
                                    break;
                                case 2:
                                    customDialog("Invalid teacher username", false);
                                    break;
                                case 3:
                                    customDialog("Invalid teacher password", false);
                                    break;
                                case 4:
                                    customDialog("Teacher username is unavailable.", false);
                                    break;
                                case 5:
                                    customDialog("Course name is unavailable.", false);
                                    break;
                                case 6:
                                    customDialog("Password required for new teacher.", false);
                                    break;
                            }
                        }
                    }
                });

                return false;
            });

            rightColumn.append(courseCreationForm);

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
