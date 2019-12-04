import java.io.File

// index, computeTime, period, deadline, priority, preemptionThresholds
// if preemptionThreshold = priority for each i, then result is preemptive, priority-based scheduling
// if preemptionThreshold = n for each i, then result is non-preemptive, priority-based scheduling
data class Task(val i: Int, val C: Int, val T: Int, val D: Int, val priority: Int?, var preemptionThreshold: Int?)
data class TaskSet(val n: Int, val m: Int, val tasks: List<Task>)

// see slide 12 of lecture 9 for fixed priority, preemptive scheduling
// pi_i = static priority
// gamma_i = dynamic priority

data class FeasibilityAnalysis(val wcrt: Map<Task, Int>, val isDeadlineMet: Map<Task, Boolean>, val isFeasible: Boolean) {
    override fun toString(): String {
        return """
FeasibilityAnalysis:
===================
${wcrt.map { (t, r) -> "wcrt of task $t = ${r} (${if (r < t.D) "" else "NOT "}feasible as wcrt <= deadline ($r < ${t.D}) for the task)" }.joinToString("\n")}

${if (isFeasible) "Since all tasks wcrt meet their deadline, this task set is feasible." else "This task set is NOT feasible since one or more tasks fail to meet their deadline."}
""".trimIndent()
    }
}

fun main() {

    fun printTaskHeader(fileName: String) {
        println("\n+++++++++++++++++")
        println("running $fileName.txt")
        println("+++++++++++++++++\n")
    }

    printTaskHeader("lec9_slide25_nonpreemptive")
    runAll(parseInput("lec9_slide25_nonpreemptive.txt"))
    println("\n ==> (NOTE: lec9_slide25_nonpreemptive should NOT be feasible)")

    printTaskHeader("lec9_slide25_preemptive")
    runAll(parseInput("lec9_slide25_preemptive.txt"))
    println("\n ==> (NOTE: lec9_slide25_preemptive should NOT be feasible)")

    printTaskHeader("lec9_slide25_part3_test")
    runAll(parseInput("lec9_slide25_part3_test.txt"))
    println("\n ==> (NOTE: lec9_slide25_part3_test should be feasible)")

    printTaskHeader("task1")
    runAll(parseInput("task1.txt"))
    println("\n ==> (NOTE: task1 should be feasible)")

    printTaskHeader("task2")
    runAll(parseInput("task2.txt"))
    println("\n ==> (NOTE: task2 should be feasible)")

    printTaskHeader("task3")
    runAll(parseInput("task3.txt"))
    println("\n ==> (NOTE: task3 should be feasible)")
}

fun runAll(_taskSet: TaskSet) {
    var taskSet = _taskSet

    if (taskSet.m <= 3) {
        println("task set does not include any priority assignments, applying deadline monotonic assignment algorithm")
        taskSet = applyDeadlineMonotonicAssignment(taskSet)
        println(taskSet)
    }

    if (taskSet.m <= 4) {
        println("task set does not include any preemptionThresholds, attempting to assign programmatically")
        val tryAssignThresholds = assignPreemptionThresholds(taskSet)
        when (tryAssignThresholds) {
            null -> {
                println("task set is infeasible for preemption threshold assignment")
                return
            }
            else -> {
                println("a preemption threshold assignment was created! Here is the new task set:")
                taskSet = tryAssignThresholds
                println(taskSet)
            }
        }
    }

    println()
    println("running feasibility analysis...")
    println()

    val feasibilityAnalysis = feasibilityAnalysis(taskSet)

    println(feasibilityAnalysis)
}

fun parseInput(file: String = "task1.txt"): TaskSet {
    fun split(line: String) = line.split(",").map { it.trim().toInt() }

    val lines = File("src/main/resources/${file}").readText().split("\n")
    val head = lines.first()
    val tail = lines.drop(1)

    val (n, m) = split(head)

    val tasks = tail.take(n)
        .mapIndexed { i, line ->
            val xs = split(line)
            Task(i + 1, xs[0], xs[1], xs[2], xs.getOrNull(3), xs.getOrNull(4))
        }

    return TaskSet(n, m, tasks)
}

val x = mutableSetOf<Int>()

/**
 * Use response time analysis
 */
fun feasibilityAnalysis(taskSet: TaskSet): FeasibilityAnalysis {
    assert(taskSet.tasks.all { it.priority != null && it.preemptionThreshold != null })

    // implementation from lec 9 pdf, page 24
    fun WCRT(taskSet: TaskSet): List<Pair<Task, Int>> {

        val output: MutableList<Pair<Task, Int>> = mutableListOf()

        var m = -1 // set later, has NOTHING to do with taskset's m which is number of variables per row
        val n = taskSet.n

        fun t_(i: Int): Task = taskSet.tasks.find { it.i == i }!!
        fun C_(i: Int) = t_(i).C
        fun T_(i: Int) = t_(i).T

        // blocking time (lecture 9 pdf, page 19)
        // given task i, return  max (j.computeTime / j.preemptionThreshold) >= i.priority > j.priority
        fun B(task: Task): Int = taskSet.tasks
            .filter { it.preemptionThreshold != null }
            .filter { t_j -> t_j.preemptionThreshold!! >= task.priority!! && task.priority > t_j.priority!! }
            .map { c_j -> c_j.C }
            .max() ?: 0

        fun S(i: Int, q: Int): Int {
            var last_ans = 0

            while (true) {
                val ans = B(t_(i)) + (q-1) * C_(i) +
                        (1..n)
                            .map { j -> t_(j) }
                            .filter { t_j -> t_j.priority!! > t_(i).priority!! }
                            .map { t_j -> (1 + (last_ans / t_j.T)) * t_j.C }
                            .sum()

                if (ans == last_ans) {
                    if (!x.contains(i)) {
                        println("blocking time for task $i is $ans")
                        x.add(i)
                    }
                    return ans
                } else if (ans > t_(i).D) {
                    if (!x.contains(i)) {
                        println("blocking time for task $i is $ans")
                        x.add(i)
                    }
                    return ans
                } else {
                    last_ans = ans
                }
            }
        }

        fun F(i: Int, q: Int): Int {

            var last_ans = S(i, q) + C_(i)

            while (true) {
                val ans = S(i, q) + C_(i) + taskSet.tasks
                    .filter { t_(i).preemptionThreshold != null && it.priority != null }
                    .filter { it.priority!! > t_(i).preemptionThreshold!! }
                    .map { t_j -> ( divCeil(last_ans, t_j.T)-(1 + (S(i, q) / t_j.T)) ) * t_j.C }
                    .sum()

                if (ans == last_ans) {
                    m = q
                    return ans
                } else if (ans <= t_(i).D && ans > F(i, q+1)) {
                    m = q
                    return ans
                } else {
                    last_ans = ans
                }
            }
        }

        fun R(i: Int): Int = (1..m).map { q -> F(i, q) - (q - 1)*T_(i) }.max()!!

        for (t_i in taskSet.tasks) {
            val i = t_i.i
            m = -1
            var done = false
            var q = 1
            var ans = -1

            while (!done) {
                ans = F(i, q)
                if (ans <= q * T_(i)) {
                    done = true
                    m = q
                } else {
                    q += 1
                }
            }
            output.add(Pair(t_i, R(i)))
        }

        return output.toList()
    }

    val wcrt = WCRT(taskSet)
    val isDeadlineMetMap = wcrt.toMap().mapValues { (t_i, r_i) -> r_i <= t_i.D  }
    val isFeasible = wcrt.all { (t_i, r_i) -> r_i <= t_i.D }

    return FeasibilityAnalysis(wcrt.toMap(), isDeadlineMetMap, isFeasible)
}

fun divCeil(n: Int, divisor: Int): Int {
    assert(n >= 0)
    assert(divisor > 0)
    return (n + divisor - 1) / divisor
}

fun applyDeadlineMonotonicAssignment(taskSet: TaskSet): TaskSet {
    val n = taskSet.n
    val priorityMap = taskSet.tasks.map { task -> task to n - taskSet.tasks.filter { it.D < task.D }.count() }.toMap()

    return taskSet.copy(tasks = taskSet.tasks.map { task ->
        task.copy(priority = priorityMap[task])
    })
}

fun assignPreemptionThresholds(initialTaskSet: TaskSet): TaskSet? {
    // force preemptionThresholds to match priority and then
    val taskSet = initialTaskSet.copy()

    val n = taskSet.n

    fun updatePreemptionThreshold(t_i: Task, pt_i: Int) {
        taskSet.tasks.find { it == t_i }!!.preemptionThreshold = pt_i
    }

    // force preemptionThresholds to match priority and then
    taskSet.tasks.forEach { it.preemptionThreshold = taskSet.n }

    fun wcrt(t_i: Task): Int = feasibilityAnalysis(taskSet).wcrt[t_i]!!

    for (i in 1..n) {
        val t_i = taskSet.tasks.find { it.priority == i }!!
        val d_i = t_i.D

        var pt_i = t_i.priority!!
        updatePreemptionThreshold(t_i, pt_i)

        var r_i = wcrt(t_i)

        while (r_i > d_i) { // while not schedulable
            pt_i++ // increase threshold
            updatePreemptionThreshold(t_i, pt_i)
            if (pt_i > n) {
                return null // system not schedulable
            }
            r_i = wcrt(t_i)
        }
    }

    return taskSet
}