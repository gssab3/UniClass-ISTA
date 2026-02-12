package it.unisa.uniclass.orari.service;

import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.model.Resto;
import it.unisa.uniclass.orari.service.dao.RestoRemote;
import jakarta.ejb.EJB;
import jakarta.ejb.Stateless;
import jakarta.persistence.NoResultException;
import java.util.List;

@Stateless
public class RestoService {

    @EJB(beanName = "RestoDAO")
    private RestoRemote restoDao;

    public RestoService() {
    }

    // Just for tests
    public RestoService(RestoRemote restoDao) {
        this.restoDao = restoDao;
    }

    public List<Resto> trovaRestiCorsoLaurea(CorsoLaurea corsoLaurea) {
        return restoDao.trovaRestiCorsoLaurea(corsoLaurea);
    }

    public List<Resto> trovaRestiCorsoLaurea(String nomeCorsoLaurea) {
        return restoDao.trovaRestiCorsoLaurea(nomeCorsoLaurea);
    }

    public List<Resto> trovaResto(String nomeResto) {
        return restoDao.trovaResto(nomeResto);
    }

    public Resto trovaResto(long id) {
        try {
            return restoDao.trovaResto(id);
        } catch (NoResultException e) {
            return null;
        }
    }

    public Resto trovaRestoNomeCorso(String nomeResto, CorsoLaurea corso) {
        try {
            return restoDao.trovaRestoNomeCorso(nomeResto, corso);
        } catch (NoResultException e) {
            return null;
        }
    }

    public Resto trovaRestoNomeCorso(String nomeResto, String nomeCorso) {
        try {
            return restoDao.trovaRestoNomeCorso(nomeResto, nomeCorso);
        } catch (NoResultException e) {
            return null;
        }
    }

    public void aggiungiResto(Resto resto) {
        if (resto != null) {
            restoDao.aggiungiResto(resto);
        }
    }

    public void rimuoviResto(Resto resto) {
        if (resto != null) {
            restoDao.rimuoviResto(resto);
        }
    }
}