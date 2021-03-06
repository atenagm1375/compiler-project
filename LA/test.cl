--node class
class Node {
  key : String;
  next : Node;
  init(str : String) : Object { key <- str };
  append(n : Node) : Object { next <- n };
  get_key() : String { key };
  get_next() : Node { next };
};

(* This is stack class (* for
stack *)
*)

class Stack {
  stack : Node;
  n : Int <- 0;
  len() : Int { n };
  push(c : String) : Object {
    let temp : Node in
    {
      n <- n + 1;
      temp <- new Node;
      temp.init(c);
      if n = 1 then stack <- $temp else {
        temp.append(stack);
        stack <- temp;
      } fi;
    }
  };
  pop() : String {
    let ret : String in
    {
      n <- n - 1;
      ret <- stack.get_key();
      stack <- stack.get_next();
      ret;
    }
  };
  display() : Object {
    let temp : Node, io : IO <- new IO in
    {
      temp <- stack;
      while not isvoid temp loop {
        io.out_string(temp.get_key().concat('\n'));
        temp <- temp.get_next();
      } pool;
    }
  };
};

class StackCommand {
  stack : Stack;
  add(s : Stack) : Stack {
    let x : Int, y : Int, convert : A2I in
    {
      stack <- s;
      convert <- new A2I;
      x <- convert.a2i(stack.pop());
      y <- convert.a2i(stack.pop());
      stack.push(convert.i2a(x + y));
      stack;
    }
  };
  swap(s : Stack) : Stack {
    let a : String, b : String in
    {
      stack <- s;
      a <- stack.pop();
      b <- stack.pop();
      stack.push(a);
      stack.push(b);
      stack;
    }
  };
  display(s : Stack) : Object { s.display() };
};

class Evaluate inherits StackCommand {
  init(s : Stack) : Stack {
    let c : String in
    {
      stack <- s;
      c <- stack.pop();
      if c = "s
      then swap(stack) else {
        if c = "+" then add(stack) else stack.push(c) fi;
      } fi;
      stack;
    }
  };
};

class Main inherits IO {
  command : String;
  s : Stack <- new Stack;
  e : Evaluate <- new Evaluate;
  main() : Object {
    {
      out_string(">\g ");
      command <- in_string();
      while not (command = "x") loop {
        if command = "e" then s <- e.init(s) else {
          if command = "d" then e.display(s) else s.push(command) fi;
        } fi;
        out_string(">\f");
        command <- in_string();
      } pool;
    }
  };
};
(*end of program
