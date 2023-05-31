#include "CFGVisitor.hpp"
#include <fstream>
#include "Library.hpp"
ifstream infile;
ofstream outfile;
class CFGASTConsumer : public ASTConsumer {
public:
    explicit CFGASTConsumer(ASTContext *context) : visitor(context,CFGVisitor::VisitorState::Main) {}

    virtual void HandleTranslationUnit(ASTContext &context) {
        CFGVisitor Function_Visitor(&context,CFGVisitor::VisitorState::Collect_All_Function);
        Function_Visitor.TraverseDecl(context.getTranslationUnitDecl());
        visitor.TraverseDecl(context.getTranslationUnitDecl());
        visitor.Dump_Annotated_file();
        infile.close();
        outfile.close();
    }

private:
    CFGVisitor visitor;
};


class CFGFrontendAction : public ASTFrontendAction {
protected:
    unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &ci,StringRef) {
        return make_unique<CFGASTConsumer>(&ci.getASTContext());
    }
};


static cl::OptionCategory ToolCategory("CFG Tool Options");
cl::opt<string> InputFilename(cl::Positional, cl::desc("<input file>"), cl::Required,cl::cat(ToolCategory));
cl::opt<string> OutputFilename(cl::Positional, cl::desc("<output file>"), cl::Required,cl::cat(ToolCategory));
cl::opt<bool> EnableFeature("enable-feature", cl::desc("Enable specific feature"), cl::init(false));
#ifndef USE_LSTINGX_MAIN
int main(int argc,const char **argv) {
    cl::HideUnrelatedOptions(ToolCategory);
    cl::ParseCommandLineOptions(argc, argv);

    vector<string> sources;
    string InputFile=InputFilename.getValue();
    string OutputFile=OutputFilename.getValue();
    infile.open(InputFile);
    outfile.open(OutputFile);
    if (!infile){
        LOG_WARNING("Could not open the file"+InputFile);
        return 1;
    }
    if (!outfile){
        LOG_WARNING("Could not open the file"+OutputFile);
        return 1;
    }
    sources.push_back(InputFile);
    
    string errorMsg;
    int remainingArgc = argc;
    auto compilationDB = FixedCompilationDatabase::loadFromCommandLine(remainingArgc, argv, errorMsg);
    if (!compilationDB) {
        outs() << "[info] Using default compilation options.\n";
        SmallString<256> currentDir;
        sys::fs::current_path(currentDir);
        compilationDB = make_unique<FixedCompilationDatabase>(Twine(currentDir), ArrayRef<string>());
    }

    ClangTool tool(*compilationDB, sources);
    return tool.run(newFrontendActionFactory<CFGFrontendAction>().get());
}
#endif
