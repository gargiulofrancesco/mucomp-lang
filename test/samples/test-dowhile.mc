component EntryPoint provides App {
  def main() : int {
    var n:int;
    n=0;
    var b:bool;
    b=true;
    
    //the statement is executed at least once
    do{
      n=2;
      b=false;
    } while(b);
    
    print(n);
    
    //the "do" block begins a deeper lexical scope
    do{
      var n:int;
      n=42;
      print(n);
    } while(n!=2);
    
    print(n);
    
    
    
    
  }
}
