

class Tag:
    def __init__(self, counter_example, contexts):
        self.counter_example = counter_example
        self.contexts = contexts
        self.tags = list()
        self.compute_tag()

    def compute_tag(self):
        for context in self.contexts.get_formated_contexts(): # 由于context在contexts的list中的位置是固定的，所以这里生成的tag的位置也是固定的
            tag = context & self.counter_example
            self.tags.append(tag)

    def get_tags(self):
        return self.tags