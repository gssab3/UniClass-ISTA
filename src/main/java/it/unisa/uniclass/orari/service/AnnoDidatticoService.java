package it.unisa.uniclass.orari.service;

import it.unisa.uniclass.orari.model.AnnoDidattico;
import it.unisa.uniclass.orari.service.dao.AnnoDidatticoRemote;
import jakarta.ejb.EJB;
import jakarta.ejb.Stateless;
import jakarta.persistence.NoResultException;
import java.util.List;

@Stateless
public class AnnoDidatticoService {

    @EJB(beanName = "AnnoDidatticoDAO")
    private AnnoDidatticoRemote annoDidatticoDao;

    public AnnoDidatticoService() {
    }

    // Costruttore per test (iniezione manuale del DAO) -- ONLY TEST
    public AnnoDidatticoService(AnnoDidatticoRemote annoDidatticoDao) {
        this.annoDidatticoDao = annoDidatticoDao;
    }

    public List<AnnoDidattico> trovaAnno(String anno) {
        return annoDidatticoDao.trovaAnno(anno);
    }

    public AnnoDidattico trovaId(int id) {
        try {
            return annoDidatticoDao.trovaId(id);
        } catch (NoResultException e) {
            return null;
        }
    }

    public List<AnnoDidattico> trovaTutti() {
        return annoDidatticoDao.trovaTutti();
    }

    public void aggiungiAnno(AnnoDidattico annoDidattico) {
        annoDidatticoDao.aggiungiAnno(annoDidattico);
    }

    public void rimuoviAnno(AnnoDidattico annoDidattico) {
        annoDidatticoDao.rimuoviAnno(annoDidattico);
    }

    public List<AnnoDidattico> trovaTuttiCorsoLaurea(long id) {
        return annoDidatticoDao.trovaTuttiCorsoLaurea(id);
    }

    public AnnoDidattico trovaTuttiCorsoLaureaNome(long id, String anno) {
        try {
            return annoDidatticoDao.trovaCorsoLaureaNome(id, anno);
        } catch (NoResultException e) {
            return null;
        }
    }
}