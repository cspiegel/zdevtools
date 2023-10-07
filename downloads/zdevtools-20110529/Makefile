SUBDIRS=	za zd

.PHONY: subdirs $(SUBDIRS)

subdirs: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@

clean:
	for subdir in $(SUBDIRS); do $(MAKE) -C $$subdir clean; done
