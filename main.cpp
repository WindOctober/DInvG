#include "CFGVisitor.hpp"

class CFGASTConsumer : public ASTConsumer {
public:
    explicit CFGASTConsumer(ASTContext *context) : visitor(context,CFGVisitor::VisitorState::Main) {}

    virtual void HandleTranslationUnit(ASTContext &context) {
        CFGVisitor Function_Visitor(&context,CFGVisitor::VisitorState::Collect_All_Function);
        Function_Visitor.TraverseDecl(context.getTranslationUnitDecl());
        visitor.TraverseDecl(context.getTranslationUnitDecl());
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
cl::opt<bool> EnableFeature("enable-feature", cl::desc("Enable specific feature"), cl::init(false));

int main(int argc,const char **argv) {
    cl::HideUnrelatedOptions(ToolCategory);
    cl::ParseCommandLineOptions(argc, argv);

    vector<string> sources;
    sources.push_back(InputFilename.getValue());

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
