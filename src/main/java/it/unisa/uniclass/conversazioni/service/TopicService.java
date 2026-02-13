package it.unisa.uniclass.conversazioni.service;

import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.dao.TopicRemote;
import jakarta.ejb.EJB;
import jakarta.ejb.Stateless;
import jakarta.persistence.NoResultException;
import java.util.List;

@Stateless
public class TopicService {

    @EJB(beanName = "TopicDAO")
    private TopicRemote topicDao;

    public TopicService() {
    }

    public TopicService(TopicRemote topicDao) {
        this.topicDao = topicDao;
    }

    public Topic trovaId(long id) {
        try {
            return topicDao.trovaId(id);
        } catch (NoResultException e) {
            return null;
        }
    }

    public Topic trovaNome(String nome) {
        try {
            return topicDao.trovaNome(nome);
        } catch (NoResultException e) {
            return null;
        }
    }

    public Topic trovaCorsoLaurea(String nome) {
        try {
            return topicDao.trovaCorsoLaurea(nome);
        } catch (NoResultException e) {
            return null;
        }
    }

    public Topic trovaCorso(String nome) {
        try {
            return topicDao.trovaCorso(nome);
        } catch (NoResultException e) {
            return null;
        }
    }

    public List<Topic> trovaTutti() {
        return topicDao.trovaTutti();
    }

    public void aggiungiTopic(Topic topic) {
        topicDao.aggiungiTopic(topic);
    }

    public void rimuoviTopic(Topic topic) {
        topicDao.rimuoviTopic(topic);
    }
}