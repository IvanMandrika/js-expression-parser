"use strict"

function abstractConstructor(constructor, evaluate, diff, toString, prefix = toString, postfix = toString) {
    constructor.prototype.evaluate = evaluate
    constructor.prototype.toString = toString
    constructor.prototype.prefix = prefix
    constructor.prototype.diff = diff
    constructor.prototype.postfix = postfix

    return constructor
}


const mapOfOperations = {}

const abstractOperationExecutor = abstractConstructor(
    function (...args) {
        this.args = args
    },
    function (...variables) {
        return this.operationFunction(...this.args.map(element => element.evaluate(...variables)))
    },
    function (string) {
        return this.operationDiff(string, ...this.args)
    },
    function () {
        return this.args.join(" ") + " " + this.nameString
    },
    function () {
        return "(" + this.nameString + " " + this.args.map(element => element.prefix()).join(" ") + ")"
    },
    function () {
        return "(" + this.args.map(element => element.postfix()).join(" ") + " " + this.nameString + ")"
    }
)

const abstractOperation = function (operationFunction, nameString, arity, operationDiff) {
    const constructor = function (...args) {
        abstractOperationExecutor.call(this, ...args)
    }
    constructor.prototype = Object.create(abstractOperationExecutor.prototype)
    constructor.prototype.operationFunction = operationFunction
    constructor.prototype.nameString = nameString
    constructor.prototype.operationDiff = operationDiff
    mapOfOperations[nameString] = [constructor, arity]
    return constructor
}

const varSymbols = ["x", "y", "z"]

const Const = abstractConstructor(
    function (val) {
        this.value = val
    },
    function () {
        return this.value
    },
    function () {
        return new Const(0)
    },
    function () {
        return this.value.toString()
    },
    function () {
        return this.value.toString()
    }
)

const Variable = abstractConstructor(
    function (name) {
        this.name = name
    },
    function (...args) {
        return args[varSymbols.indexOf(this.name)]
    },
    function (string) {
        return new Const(string === this.name ? 1 : 0)
    },
    function () {
        return this.name
    },
)

const zero = new Const(0)
const one = new Const(1)
const two = new Const(2)


const Add = abstractOperation((a, b) => a + b, "+", 2,
    (string, a, b) => new Add(a.diff(string), b.diff(string)))

const Subtract = abstractOperation((a, b) => a - b, "-", 2,
    (string, a, b) => new Subtract(a.diff(string), b.diff(string)))

const Multiply = abstractOperation((a, b) => a * b, "*", 2,
    (string, a, b) => new Add(new Multiply(a.diff(string), b), new Multiply(a, b.diff(string))))

const Divide = abstractOperation((a, b) => a / b, "/", 2,
    (string, a, b) => new Divide(new Subtract(new Multiply(a.diff(string), b), new Multiply(a, b.diff(string))), new Multiply(b, b)))

const Negate = abstractOperation(a => -a, "negate", 1,
    (string, a) => new Negate(a.diff(string)))

const Hypot = abstractOperation((a, b) => a * a + b * b, "hypot", 2,
    (string, a, b) => new Multiply(two, new Add(new Multiply(a, a.diff(string)), new Multiply(b, b.diff(string)))))

const HMean = abstractOperation((a, b) => 2 / (1 / a + 1 / b), "hmean", 2,
    (string, a, b) => new Multiply(two, new Divide( new Add(new Multiply(new Multiply(a, a), b.diff(string)),
            new Multiply(new Multiply(b, b), a.diff(string))), new Multiply(new Add(a, b), new Add(a, b)))))

const ArithMean = abstractOperation((...args) => args.reduce((a, b) => a + b) / args.length, "arithMean", 0,
    (string, ...args) => new Divide(args.reduce((a, b) => new Add(a, b)).diff(string), new Const(args.length)))

const GeomMean = abstractOperation((...args) => {
        const result = args.reduce((a, b) => a * b)
        return result < 0 ? ((-result) ** (1 / args.length)) : (result ** (1 / args.length))
    }, "geomMean", 0,
    (string, ...args) => {
        let result = one
        for (let i = 0; i < args.length - 1; i++) {
            result = new Multiply(result, new GeomMean(...args))
        }
        return (new Divide(new Multiply(new Const(1 / args.length), (args.reduce((a, b) => new Multiply(a, b)))).diff(string),
            result))
    })

const HarmMean = abstractOperation(((...args) => args.length * args.reduce((a, b) => 1 / ((a === Infinity ? 0 : 1 / a) + 1 / b))), "harmMean", 0,
    (string, ...args) => new Divide(new Const(args.length), args.reduce((a, b) => new Add(a, new Divide(one, b)), zero)).diff(string))

function ExpressionParseError(message) {
    this.message = message
}

ExpressionParseError.prototype = Object.create(Error.prototype)
ExpressionParseError.prototype.constructor = ExpressionParseError
ExpressionParseError.prototype.name = "ParseError"


const parseAbstract = (expression, errors = false, reverse = false) => {
    const stack = [];
    let balance = 0;
    const bracketStack = [];
    while (expression.length !== 0) {
        if (expression[0] in mapOfOperations) {
            if (errors && expression[1] !== (reverse ? "(" : ")")) throw new ExpressionParseError("Not enough operations, near parent")
            if (errors && stack.length < mapOfOperations[expression[0]][1]) throw new ExpressionParseError("Not enough operands, you need " + mapOfOperations[expression[0]][1] + " operands")
            stack.push(new mapOfOperations[expression[0]][0](...(reverse ? stack.splice(
                    (mapOfOperations[expression[0]][1] !== 0 ? stack.length - mapOfOperations[expression[0]][1] : bracketStack[0] - stack.length)).reverse()
                : stack.splice(mapOfOperations[expression[0]][1] !== 0 ? stack.length - mapOfOperations[expression[0]][1] : bracketStack[0] - stack.length))))
            expression.shift()
        } else if (varSymbols.includes(expression[0]))
            stack.push(new Variable(expression.shift()))
        else if (isFinite(expression[0]))
            stack.push(new Const(parseInt(expression.shift())))
        else if (expression[0] === (reverse ? ")" : "(")) {
            balance++
            expression.shift()
            bracketStack.unshift(stack.length)
        } else if (expression[0] === (reverse ? "(" : ")")) {
            if (errors && !(stack[stack.length - 1].nameString in mapOfOperations)) throw new ExpressionParseError("Not enough operations")
            if (errors && expression[1] === (reverse ? "(" : ")")) throw new ExpressionParseError("Not enough operations, near parent")
            balance++
            expression.shift()
            if (errors &&bracketStack.shift() === undefined) throw new ExpressionParseError("Unbalanced parentheses")
        } else if (errors) throw new ExpressionParseError("Unknown token: " + expression[0])
    }
    if (errors) {
        if (bracketStack.length !== 0)
            throw new ExpressionParseError("Unbalanced parentheses")
        if (stack.length !== 1)
            throw new ExpressionParseError("Not enough operations " + stack[0].toString() + " " + stack[1].toString())
    }
    return stack.shift()
}

const parse = expression => parseAbstract(expression.split(/([()\s])/g).filter(el => !/^\s*$/.test(el)))
const parsePostfix = expression => parseAbstract(expression.split(/([()\s])/g).filter(el => !/^\s*$/.test(el)), true)
const parsePrefix = expression => parseAbstract(expression.split(/([()\s])/g).filter(el => !/^\s*$/.test(el)).reverse(), true, true)
